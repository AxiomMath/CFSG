module

public import CFSG.Milestones.ASVolI.F48.D43.ELie
public import CFSG.Milestones.ASVolI.F48.Rest.U52eLie

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable CFSG.Quasithin

@[expose] def burnsideF48dE_Q (K'' : Subgroup ↥burnsideF48dE_Xh) : Prop :=
  Nat.card ↥K'' = 156 ∧ ∀ z ∈ K'', z ∈ burnsideF48dE_Uh → z = 1

@[expose] noncomputable def burnsideF48dE_Bs : Subgroup ↥burnsideF48dE_Xh :=
  (burnsideF48d_P1 ⊓ burnsideF48d_P2).map burnsideF48dE_ι

section Class


theorem burnsideF48dE_compl_not_le (hM : burnsideF48d_ModelFacts)
    {K'' : Subgroup ↥burnsideF48dE_Xh} (hle : K'' ≤ burnsideF48dE_P1 ⊓ burnsideF48dE_P2)
    (hQ : burnsideF48dE_Q K'') : ∃ s ∈ K'', s ∉ burnsideF48dE_Xs := by
  by_contra hne
  push Not at hne
  have hKB : ∀ s ∈ K'', s ∈ burnsideF48dE_Bs := fun s hs =>
    ⟨⟨s, hne s hs⟩, burnsideF48dE_mem_B hM (hle hs) (hne s hs), rfl⟩
  have hUB : burnsideF48dE_Uh ≤ burnsideF48dE_Bs := Subgroup.map_mono hM.U_le
  let f : ↥K'' × ↥burnsideF48dE_Uh → ↥burnsideF48dE_Bs := fun p =>
    ⟨p.1 * p.2, burnsideF48dE_Bs.mul_mem (hKB _ p.1.2) (hUB p.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨k, u⟩ ⟨k', u'⟩ h
    have h' : (k : ↥burnsideF48dE_Xh) * u = k' * u' := congrArg Subtype.val h
    have hm : (k' : ↥burnsideF48dE_Xh)⁻¹ * k = u' * (u : ↥burnsideF48dE_Xh)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h', mul_inv_cancel_right]
    have h1 : (k' : ↥burnsideF48dE_Xh)⁻¹ * k = 1 :=
      hQ.2 _ (K''.mul_mem (K''.inv_mem k'.2) k.2) (by
        rw [hm]
        exact burnsideF48dE_Uh.mul_mem u'.2 (burnsideF48dE_Uh.inv_mem u.2))
    have hk : k = k' := Subtype.ext (inv_mul_eq_one.1 h1).symm
    subst hk
    have hu : u = u' := Subtype.ext (mul_left_cancel h')
    rw [hu]
  have hcard := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod, hQ.1, burnsideF48dE_Uh,
    Subgroup.card_map_of_injective (Subgroup.inclusion_injective _), hM.card_U, burnsideF48dE_Bs,
    Subgroup.card_map_of_injective (Subgroup.inclusion_injective _), hM.card_B] at hcard
  norm_num at hcard

theorem burnsideF48dE_classify (hM : burnsideF48d_ModelFacts)
    {K'' : Subgroup ↥burnsideF48dE_Xh} (hle : K'' ≤ burnsideF48dE_P1 ⊓ burnsideF48dE_P2)
    (hQ : burnsideF48dE_Q K'') :
    ∃ t ∈ burnsideF48dE_P1 ⊓ burnsideF48dE_P2, ∀ z, z ∈ K'' ↔ t * z * t⁻¹ ∈ burnsideF48dE_K := by
  haveI := burnsideF48dE_normal hM
  obtain ⟨s₀, hs₀, hs₀X⟩ := burnsideF48dE_compl_not_le hM hle hQ
  set A : Subgroup ↥burnsideF48d_X := K''.comap burnsideF48dE_ι with hA
  have hAmap : A.map burnsideF48dE_ι = burnsideF48dE_Xs ⊓ K'' := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hzX, hzK⟩
      exact ⟨⟨z, hzX⟩, hzK, rfl⟩
  have hcardA : Nat.card ↥A = 52 := by
    have h1 := Subgroup.relIndex_mul_card burnsideF48dE_Xs K''
    have h2 := Subgroup.relIndex_dvd_index_of_normal burnsideF48dE_Xs K''
    rw [burnsideF48dE_index hM] at h2
    have h3 : burnsideF48dE_Xs.relIndex K'' ≠ 1 := fun h =>
      hs₀X (Subgroup.relIndex_eq_one.1 h hs₀)
    have h4 : burnsideF48dE_Xs.relIndex K'' = 3 :=
      ((Nat.dvd_prime Nat.prime_three).1 h2).resolve_left h3
    rw [h4, hQ.1, ← hAmap, Subgroup.card_map_of_injective (Subgroup.inclusion_injective _)] at h1
    omega
  have hAle : A ≤ burnsideF48d_P1 ⊓ burnsideF48d_P2 := fun x hx =>
    burnsideF48dE_mem_B hM (hle hx) x.2
  obtain ⟨t, ht, hiff⟩ := hM.hconj A hAle hcardA
  set c : ↥burnsideF48dE_Xh := burnsideF48dE_ι t with hc
  have hcB : c ∈ burnsideF48dE_P1 ⊓ burnsideF48dE_P2 := burnsideF48dE_ι_B ht
  set K3 : Subgroup ↥burnsideF48dE_Xh := K''.map (MulAut.conj c).toMonoidHom with hK3def
  have hmemK3 : ∀ w, w ∈ K3 ↔ c⁻¹ * w * c ∈ K'' := by
    intro w
    constructor
    · rintro ⟨w', hw', rfl⟩
      have e : c⁻¹ * ((MulAut.conj c).toMonoidHom w') * c = w' := by
        show c⁻¹ * (c * w' * c⁻¹) * c = w'
        group
      rw [e]
      exact hw'
    · intro hw
      refine ⟨_, hw, ?_⟩
      show c * (c⁻¹ * w * c) * c⁻¹ = w
      group
  have hcK3 : Nat.card ↥K3 = 156 := by
    rw [hK3def, Subgroup.card_map_of_injective (MulAut.conj c).injective, hQ.1]
  have hTK3 : burnsideF48dE_Th ≤ K3 := by
    rintro _ ⟨k, hk, rfl⟩
    rw [hmemK3]
    have hk' : t⁻¹ * k * t ∈ A := (hiff _).2 (by simpa [mul_assoc] using hk)
    have e : c⁻¹ * burnsideF48dE_ι k * c = burnsideF48dE_ι (t⁻¹ * k * t) := by
      rw [hc, map_mul, map_mul, map_inv]
    rw [e]
    exact hk'
  have hK3X : ∀ w ∈ K3, w ∈ burnsideF48dE_Xs → w ∈ burnsideF48dE_Th := by
    intro w hw hwX
    have h1 := (hmemK3 w).1 hw
    have e : c⁻¹ * w * c = burnsideF48dE_ι (t⁻¹ * ⟨w, hwX⟩ * t) := by
      rw [hc, map_mul, map_mul, map_inv]
      rfl
    rw [e] at h1
    have h2 := (hiff _).1 h1
    have e2 : t * (t⁻¹ * ⟨(w : Equiv.Perm (Fin 26572)), hwX⟩ * t) * t⁻¹ =
        ⟨(w : Equiv.Perm (Fin 26572)), hwX⟩ := by group
    rw [e2] at h2
    exact ⟨_, h2, rfl⟩
  set s : ↥burnsideF48dE_Xh := c * s₀ * c⁻¹ with hsdef
  have hsK3 : s ∈ K3 := by
    rw [hmemK3]
    have e : c⁻¹ * (c * s₀ * c⁻¹) * c = s₀ := by group
    rw [e]
    exact hs₀
  have hsX : s ∉ burnsideF48dE_Xs := by
    intro h
    apply hs₀X
    have h' := (burnsideF48dE_normal hM).conj_mem _ h c⁻¹
    have e : c⁻¹ * (c * s₀ * c⁻¹) * c⁻¹⁻¹ = s₀ := by group
    rwa [e] at h'
  have hK3B : K3 ≤ burnsideF48dE_P1 ⊓ burnsideF48dE_P2 := by
    intro w hw
    have h1 := hle ((hmemK3 w).1 hw)
    have e : w = c * (c⁻¹ * w * c) * c⁻¹ := by group
    rw [e]
    exact (burnsideF48dE_P1 ⊓ burnsideF48dE_P2).mul_mem
      ((burnsideF48dE_P1 ⊓ burnsideF48dE_P2).mul_mem hcB h1)
      ((burnsideF48dE_P1 ⊓ burnsideF48dE_P2).inv_mem hcB)
  have hsB := hK3B hsK3
  have hsT : ∀ k ∈ burnsideF48dE_Th, s * k * s⁻¹ ∈ burnsideF48dE_Th := by
    intro k hk
    refine hK3X _ (K3.mul_mem (K3.mul_mem hsK3 (hTK3 hk)) (K3.inv_mem hsK3)) ?_
    have hkX : k ∈ burnsideF48dE_Xs := ((burnsideF48dE_mem_Th hM k).1 hk).1
    exact (burnsideF48dE_normal hM).conj_mem k hkX s
  obtain ⟨e, he, b, hsb⟩ := burnsideF48dE_dec hM s
  have he0 : e ≠ 0 := by
    rintro rfl
    apply hsX
    rw [hsb, pow_zero, mul_one]
    exact b.2
  have hbB : b ∈ burnsideF48d_P1 ⊓ burnsideF48d_P2 := by
    have h1 : burnsideF48dE_ι b ∈ burnsideF48dE_P1 ⊓ burnsideF48dE_P2 := by
      have := (burnsideF48dE_P1 ⊓ burnsideF48dE_P2).mul_mem hsB
        ((burnsideF48dE_P1 ⊓ burnsideF48dE_P2).inv_mem
          ((burnsideF48dE_P1 ⊓ burnsideF48dE_P2).pow_mem burnsideF48dE_F_mem_B e))
      rwa [hsb, mul_inv_cancel_right] at this
    exact burnsideF48dE_mem_B hM h1 b.2
  have hn : (burnsideF48dE_F ^ e)⁻¹ ∈
      Subgroup.normalizer (burnsideF48dE_Th : Set ↥burnsideF48dE_Xh) :=
    Subgroup.inv_mem _ (Subgroup.pow_mem _ (burnsideF48dE_F_normalizer hM) e)
  have hbT : ∀ k ∈ burnsideF48d_T, b * k * b⁻¹ ∈ burnsideF48d_T := by
    intro k hk
    have h1 := (Subgroup.mem_normalizer_iff.1 hn (burnsideF48dE_ι k)).1 ⟨k, hk, rfl⟩
    rw [inv_inv] at h1
    have h2 := hsT _ h1
    have e2 : s * ((burnsideF48dE_F ^ e)⁻¹ * burnsideF48dE_ι k * burnsideF48dE_F ^ e) * s⁻¹ =
        burnsideF48dE_ι (b * k * b⁻¹) := by
      rw [hsb, map_mul, map_mul, map_inv]
      group
    rw [e2] at h2
    exact (Subgroup.mem_map_iff_mem (Subgroup.inclusion_injective _)).1 h2
  have hbTT := hM.normalizer_T b hbB hbT
  have hFe : burnsideF48dE_F ^ e ∈ K3 := by
    have h1 : burnsideF48dE_ι b ∈ K3 := hTK3 ⟨b, hbTT, rfl⟩
    have := K3.mul_mem (K3.inv_mem h1) hsK3
    rwa [hsb, inv_mul_cancel_left] at this
  have hF : burnsideF48dE_F ∈ K3 := by
    rcases (show e = 1 ∨ e = 2 by omega) with rfl | rfl
    · rwa [pow_one] at hFe
    · have e4 : burnsideF48dE_F = (burnsideF48dE_F ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, burnsideF48dE_F_cube hM, one_mul,
          pow_one]
      rw [e4]
      exact K3.pow_mem hFe 2
  have hKle : burnsideF48dE_K ≤ K3 := sup_le hTK3 (Subgroup.zpowers_le.2 hF)
  have hEq : burnsideF48dE_K = K3 :=
    Subgroup.eq_of_le_of_card_ge hKle (by rw [hcK3, burnsideF48dE_card_K hM])
  refine ⟨c, hcB, fun z => ?_⟩
  rw [hEq, hmemK3]
  have e : c⁻¹ * (c * z * c⁻¹) * c = z := by group
  rw [e]

theorem burnsideF48dE_core
    (hM : burnsideF48d_ModelFacts) :
    burnsideF48t_ECore burnsideF48dE_P1 burnsideF48dE_P2 6 burnsideF48dE_Q := by
  intro Y _ f₁ f₂ h12 hgen hinj hcard K'' hK''le hQ x y hx hy hx2 hxK hxx hy1 hyK hyy hrel
  obtain ⟨t, ht, hiff⟩ := burnsideF48dE_classify hM hK''le hQ
  exact burnsideF48t_core_conj (burnsideF48dE_facts hM) f₁ f₂ h12 hgen hinj hcard hK''le ht hiff
    hx hy hx2 hxK hxx hy1 hyK hyy hrel

end Class

end CFSG.ASVolI
