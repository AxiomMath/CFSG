module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AW3Heis
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AW3Sign

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

variable {T : Type} [CommGroup T] [Finite T] {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
  {X : Subgroup (MulAut T)}

private theorem s16t_w3_perm_cube_mem : ∀ τ π : Equiv.Perm (Fin 3), τ ^ 3 = 1 → τ ≠ 1 →
    π ^ 3 = 1 → π = 1 ∨ π = τ ∨ π = τ ^ 2 := by
  decide

theorem s16t_w3_mem_sup (h : S16tW3Hyp Y X) {S : Subgroup (MulAut T)}
    (hS : ∀ g, g ∈ S ↔ g ∈ X ∧ (∀ i, (Y i).map g.toMonoidHom = Y i) ∧ g ^ 3 = 1)
    (hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {f : MulAut T} (hfX : f ∈ X) (hf3 : f ^ 3 = 1)
    (hfm : ∃ i, (Y i).map f.toMonoidHom ≠ Y i) {x : MulAut T} (hxX : x ∈ X) {k : ℕ}
    (hk : x ^ (3 ^ k) = 1) : x ∈ S ⊔ Subgroup.zpowers f := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ρ, hρ⟩ := s16t_a_exists_perm_hom h.injective h.perm
  have hfP : f ∈ S ⊔ Subgroup.zpowers f := Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
  have hconjP : ∀ g ∈ X, (∀ i, (Y i).map g.toMonoidHom = Y i) →
      ∀ p ∈ S ⊔ Subgroup.zpowers f, g * p * g⁻¹ ∈ S ⊔ Subgroup.zpowers f := by
    intro g hgX hg p hp
    have hle : S ⊔ Subgroup.zpowers f ≤
        (S ⊔ Subgroup.zpowers f).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun s hs => Subgroup.mem_comap.2 ?_) (Subgroup.zpowers_le.2
        (Subgroup.mem_comap.2 ?_))
      · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact Subgroup.mem_sup_left (s16t_w3_conj_mem h hS hgX hs)
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show g * f * g⁻¹ = g * f * g⁻¹ * f⁻¹ * f by group]
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_left (s16t_w3_comm_mem h hS hSc hfX hf3 hfm hgX hg)) hfP
    exact hle hp
  have hnormP : ∀ g ∈ X, (∀ i, (Y i).map g.toMonoidHom = Y i) →
      g ∈ Subgroup.normalizer ((S ⊔ Subgroup.zpowers f : Subgroup (MulAut T)) :
        Set (MulAut T)) := by
    intro g hgX hg
    rw [Subgroup.mem_normalizer_iff]
    intro p
    refine ⟨hconjP g hgX hg p, fun hp => ?_⟩
    have h1 := hconjP g⁻¹ (X.inv_mem hgX) (fun i => s16t_w3_map_inv (hg i)) _ hp
    rwa [show g⁻¹ * (g * p * g⁻¹) * g⁻¹⁻¹ = p by group] at h1
  let e : ι ≃ Fin 3 := Fintype.equivFinOfCardEq h.card_index
  have hτ3 : ρ ⟨f, hfX⟩ ^ 3 = 1 := by
    have h1 : (⟨f, hfX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hf3)
    rw [← map_pow, h1, map_one]
  have hτ1 : ρ ⟨f, hfX⟩ ≠ 1 := by
    intro h1
    obtain ⟨i₀, hi₀⟩ := hfm
    exact hi₀ ((hρ ⟨f, hfX⟩ i₀).trans (by rw [h1]; rfl))
  have hπ3 : ρ ⟨x, hxX⟩ ^ 3 = 1 := by
    have h1 : ρ ⟨x, hxX⟩ ^ (3 ^ k) = 1 := by
      have h2 : (⟨x, hxX⟩ : ↥X) ^ (3 ^ k) = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hk)
      rw [← map_pow, h2, map_one]
    have h2 : orderOf (ρ ⟨x, hxX⟩) ∣ 6 := by
      have h3 := orderOf_dvd_card (x := ρ ⟨x, hxX⟩)
      rwa [Fintype.card_perm, h.card_index] at h3
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h1)
    rw [hj] at h2
    refine orderOf_dvd_iff_pow_eq_one.1 ?_
    rw [hj]
    rcases j with _ | _ | j
    · exact one_dvd 3
    · exact dvd_rfl
    · exact absurd ((pow_dvd_pow 3 (by omega : 2 ≤ j + 2)).trans h2) (by norm_num)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ρ ⟨x, hxX⟩ = ρ (⟨f, hfX⟩ ^ n) := by
    have hc := s16t_w3_perm_cube_mem (e.permCongrHom (ρ ⟨f, hfX⟩)) (e.permCongrHom (ρ ⟨x, hxX⟩))
      (by rw [← map_pow, hτ3, map_one]) (by rw [Ne, MulEquiv.map_eq_one_iff]; exact hτ1)
      (by rw [← map_pow, hπ3, map_one])
    rcases hc with hc | hc | hc
    · exact ⟨0, by rw [(MulEquiv.map_eq_one_iff _).1 hc, pow_zero, map_one]⟩
    · exact ⟨1, by rw [e.permCongrHom.injective hc, pow_one]⟩
    · rw [← map_pow] at hc
      exact ⟨2, by rw [e.permCongrHom.injective hc, map_pow]⟩
  obtain ⟨b, hbdef⟩ : ∃ b : ↥X, b = (⟨f, hfX⟩ ^ n)⁻¹ * ⟨x, hxX⟩ := ⟨_, rfl⟩
  have hρb : ρ b = 1 := by
    rw [hbdef, map_mul, map_inv, hn, inv_mul_cancel]
  have hbeq : (b : MulAut T) = (f ^ n)⁻¹ * x := by
    rw [hbdef, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
  have hbfix : ∀ i, (Y i).map ((f ^ n)⁻¹ * x).toMonoidHom = Y i := by
    rw [← hbeq]
    exact fun i => (hρ b i).trans (by rw [hρb]; rfl)
  have hbX : (f ^ n)⁻¹ * x ∈ X := hbeq ▸ b.2
  have hfnP : f ^ n ∈ S ⊔ Subgroup.zpowers f := Subgroup.pow_mem _ hfP n
  have hxeq : x = f ^ n * ((f ^ n)⁻¹ * x) := (mul_inv_cancel_left _ _).symm
  have hxN : x ∈ Subgroup.normalizer ((S ⊔ Subgroup.zpowers f : Subgroup (MulAut T)) :
      Set (MulAut T)) := by
    rw [hxeq]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hfnP) (hnormP _ hbX hbfix)
  have hPp : IsPGroup 3 ↥(S ⊔ Subgroup.zpowers f) :=
    IsPGroup.of_card (s16t_w3_isPOnePlusTwo_sup h hS hSc hfX hf3 hfm).2.1
  have hxp : IsPGroup 3 ↥(Subgroup.zpowers x) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  have hQ := IsPGroup.to_sup_of_normal_left' hPp hxp (Subgroup.zpowers_le.2 hxN)
  have hbQ : (f ^ n)⁻¹ * x ∈ (S ⊔ Subgroup.zpowers f) ⊔ Subgroup.zpowers x :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hfnP))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  obtain ⟨m, hm⟩ := hQ ⟨_, hbQ⟩
  have hbm : ((f ^ n)⁻¹ * x) ^ (3 ^ m) = 1 := by
    have h1 := congrArg Subtype.val hm
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h1
  have hbS := s16t_w3_mem_S_of_pow h hS hbX hbfix hbm
  rw [hxeq]
  exact Subgroup.mul_mem _ hfnP (Subgroup.mem_sup_left hbS)

theorem s16t_w3_isPOnePlusTwo_pCoreOf (h : S16tW3Hyp Y X) {f : MulAut T} (hfX : f ∈ X)
    (hf3 : f ^ 3 = 1) (hfm : ∃ i, (Y i).map f.toMonoidHom ≠ Y i) :
    IsPOnePlusTwo 3 ↥(CFSG.Open.pCoreOf 3 X) := by
  obtain ⟨S, hS, hSc⟩ := s16t_w3_exists_S h
  have hP := s16t_w3_isPOnePlusTwo_sup h hS hSc hfX hf3 hfm
  have hPX : S ⊔ Subgroup.zpowers f ≤ X :=
    sup_le (fun s hs => ((hS s).1 hs).1) (Subgroup.zpowers_le.2 hfX)
  have hP3 : ∀ x ∈ S ⊔ Subgroup.zpowers f, x ^ 3 = 1 := fun x hx =>
    congrArg Subtype.val (hP.2.2 ⟨x, hx⟩)
  have hnorm : ((S ⊔ Subgroup.zpowers f).subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine s16t_w3_mem_sup h hS hSc hfX hf3 hfm (X.mul_mem (X.mul_mem g.2 n.2) (X.inv_mem g.2))
      (k := 1) ?_
    rw [pow_one, conj_pow, hP3 _ hn, mul_one, mul_inv_cancel]
  have hPp : IsPGroup 3 ↥(S ⊔ Subgroup.zpowers f) := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one]; exact hP3 x.1 x.2)⟩
  have heq : CFSG.Open.pCoreOf 3 X = S ⊔ Subgroup.zpowers f := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 3) (G := ↥X)) ⟨y, hy⟩
      have h1 : y ^ (3 ^ k) = 1 := congrArg Subtype.val hk
      have h2 : (y : MulAut T) ^ (3 ^ k) = 1 := congrArg Subtype.val h1
      exact s16t_w3_mem_sup h hS hSc hfX hf3 hfm y.2 h2
    · have hle : (S ⊔ Subgroup.zpowers f).subgroupOf X ≤ CFSG.pCore 3 ↥X := by
        rw [CFSG.pCore_eq_iSup]
        exact le_iSup_of_le ((S ⊔ Subgroup.zpowers f).subgroupOf X)
          (le_iSup_of_le hnorm (le_iSup_of_le
            (hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPX).symm) le_rfl))
      rw [← Subgroup.map_subgroupOf_eq_of_le hPX]
      exact Subgroup.map_mono hle
  rw [heq]
  exact hP

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
