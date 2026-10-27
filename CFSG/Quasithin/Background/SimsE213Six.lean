module

public import CFSG.Quasithin.Background.SimsE213M
public import CFSG.Quasithin.Vol2.E2ThirteenSix

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem e213_six {Γ : Type} [Group Γ] [Finite Γ]
    (H T M V : Subgroup Γ) (h : E2.Hyp28 H T M V) (hc : CharTwo H) (I : Subgroup Γ)
    (hI : IsInIHTV H T M V I) :
    (∀ x : Γ, (∃ i ∈ I, ∃ v ∈ V, x = i⁻¹ * v * i) → x ∈ T →
        x ∈ Subgroup.centralizer (V : Set Γ)) →
      ¬ ∃ k : ℕ, 1 ≤ k ∧ IsSp4Full k (E2.StarQuot (M ⊓ I) I) := by
  rintro hconj ⟨k, -, hSp⟩
  have := E2P.finite_starQuot (M ⊓ I) I
  have hI' := E213M.noRoot_of_isInIHTV hI
  obtain ⟨g, hg, hgen⟩ := hI'.2.1
  have hsyl := hI.2.2.1
  have hp := h.pair_of_member hI' hg hgen
  have hcharI : CharTwo I := by
    have := E2.charTwo_of_charTwo h (hI.1 hg) hc
    rwa [← hgen] at this
  set B := kerIn (M ⊓ I) I ⊓ V with hB
  set NB := Subgroup.normalizer ((B : Subgroup Γ) : Set Γ) with hNB
  have hkey : ∀ x ∈ I, B6.conjSub x V ≤ T → x ∈ NB := fun x hx hxT =>
    hp.mem_normalizer_of_conj_le_centralizer hx fun w hw =>
      hconj w ⟨x⁻¹, I.inv_mem hx, x⁻¹ * w * x, B6.mem_conjSub.mp hw, by group⟩ (hxT hw)
  have hTN : T ⊓ I ≤ NB := fun t ht =>
    hkey t ht.2 ((B6.conjSub_eq_self (h.normal_T ht.1)).le.trans h.le_T)
  have hJN : kerIn (M ⊓ I) I ≤ NB := by
    intro j hj
    have hjI : j ∈ I := kerIn_le.trans hp.le_X hj
    refine hkey j hjI fun w hw => ?_
    rw [B6.mem_conjSub] at hw
    have hc := hp.commutator_kerIn_mem_pCoreOf hw hj
    have e : w = (j⁻¹ * w * j * j * (j⁻¹ * w * j)⁻¹ * j⁻¹)⁻¹ * (j⁻¹ * w * j) := by group
    rw [e]
    exact T.mul_mem (T.inv_mem ((hp.pCoreOf_le_T hc).1)) (h.le_T hw)
  have hVZ := E2.e2_11_two h hI' hp.V_le
  have hVT : E2.star (M ⊓ I) I V ≤ E2.star (M ⊓ I) I (T ⊓ I) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono I hp.le_T)
  have hS := E2.isSylowTwoOf_star_inf (M := M) hsyl
  have hgenS := E2.Sp4Z.closure_conj_center_eq_top hSp hS
  have himg : (⊤ : Subgroup (E2.StarQuot (M ⊓ I) I)) ≤ E2.star (M ⊓ I) I (I ⊓ NB) := by
    rw [← hgenS, Subgroup.closure_le]
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((kerIn (M ⊓ I) I).subgroupOf I) y
    refine ⟨x, Subgroup.mem_subgroupOf.2 ⟨x.2, ?_⟩, rfl⟩
    set Q₀ := (T ⊓ I) ⊔ kerIn (M ⊓ I) I with hQ₀
    have hQ₀I : Q₀ ≤ I := sup_le inf_le_right (kerIn_le.trans hp.le_X)
    have hVxQ : B6.conjSub (x : Γ) V ≤ Q₀ := by
      intro w hw
      have hvV : (x : Γ)⁻¹ * w * x ∈ V := B6.mem_conjSub.mp hw
      have hvI : (x : Γ)⁻¹ * w * x ∈ I := hp.V_le hvV
      have hwI : w ∈ I := by
        have := I.mul_mem (I.mul_mem x.2 hvI) (I.inv_mem x.2)
        simpa [mul_assoc] using this
      set q := QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) with hq
      have hvs : q ⟨(x : Γ)⁻¹ * w * x, hvI⟩ ∈ E2.star (M ⊓ I) I (T ⊓ I) ⊓
          Subgroup.centralizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)) :=
        ⟨hVT ⟨_, Subgroup.mem_subgroupOf.2 hvV, rfl⟩, hVZ ⟨_, Subgroup.mem_subgroupOf.2 hvV, rfl⟩⟩
      have h1 := hy _ hvs
      have e1 : q x * q ⟨(x : Γ)⁻¹ * w * x, hvI⟩ * (q x)⁻¹ = q ⟨w, hwI⟩ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        show (x : Γ) * ((x : Γ)⁻¹ * w * x) * (x : Γ)⁻¹ = w
        group
      rw [e1] at h1
      obtain ⟨t, ht, hte⟩ := h1
      have hte' : (QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) t : E2.StarQuot (M ⊓ I) I) =
          QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) ⟨w, hwI⟩ := hte
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf] at hte'
      have htJ : (t : Γ)⁻¹ * w ∈ kerIn (M ⊓ I) I := by simpa using hte'
      have e2 : w = (t : Γ) * ((t : Γ)⁻¹ * w) := by group
      rw [e2]
      exact Q₀.mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 ht))
        (Subgroup.mem_sup_right htJ)
    have hVx2 : IsPGroup 2 (B6.conjSub (x : Γ) V) :=
      (B6.isPGroup_of_isElemAbelian h.elem).map _
    obtain ⟨S', hS', hVS'⟩ := B6.exists_isSylowTwoOf_ge hVx2 hVxQ
    have hTQ : IsSylowTwoOf (T ⊓ I) Q₀ := B6.isSylowTwoOf_mono hsyl le_sup_left hQ₀I
    obtain ⟨y, hyQ, hyS⟩ := B6.isSylowTwoOf_exists_conj hTQ hS'
    have hyN : y ∈ NB := sup_le hTN hJN hyQ
    have hyI : y ∈ I := hQ₀I hyQ
    have hT' : B6.conjSub (y⁻¹ * x) V ≤ T := by
      intro w hw
      rw [B6.mem_conjSub] at hw
      have h3 : y * w * y⁻¹ ∈ S' := by
        apply hVS'
        rw [B6.mem_conjSub]
        simpa [mul_assoc] using hw
      rw [hyS, B6.mem_conjSub] at h3
      have h4 := h3.1
      simpa [mul_assoc] using h4
    have h5 := hkey _ (I.mul_mem (I.inv_mem hyI) x.2) hT'
    have e3 : (x : Γ) = y * (y⁻¹ * x) := by group
    rw [e3]
    exact NB.mul_mem hyN h5
  obtain ⟨n, hn, hne⟩ := himg (Subgroup.mem_top
    (QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) ⟨g, hg⟩))
  replace hn : (n : Γ) ∈ I ⊓ NB := hn
  have hne' : (QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) n : E2.StarQuot (M ⊓ I) I) =
      QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) ⟨g, hg⟩ := hne
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at hne'
  have hgJ : (n : Γ)⁻¹ * g ∈ kerIn (M ⊓ I) I := by simpa using hne'
  have hgN : g ∈ NB := by
    have e : g = (n : Γ) * ((n : Γ)⁻¹ * g) := by group
    rw [e]
    exact NB.mul_mem hn.2 (hJN hgJ)
  have hIV : I ≠ V := by
    intro hIV
    obtain ⟨F, _, _, _, ⟨θ⟩⟩ := E2.Sp4Z.exists_mulEquiv_antiSp_of_isSp4C hSp
    apply E2.Sp4Z.swapElt01_mul_swapElt12_ne (K := F)
    obtain ⟨a, ha⟩ := θ.surjective E2.Sp4Z.swapElt01
    obtain ⟨b, hb⟩ := θ.surjective E2.Sp4Z.swapElt12
    obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective ((kerIn (M ⊓ I) I).subgroupOf I) a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective ((kerIn (M ⊓ I) I).subgroupOf I) b
    have hab : a' * b' = b' * a' := by
      have ha'V : (a' : Γ) ∈ V := hIV ▸ a'.2
      have hb'V : (b' : Γ) ∈ V := hIV ▸ b'.2
      exact Subtype.ext (hp.comm ha'V hb'V)
    rw [← ha, ← hb, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hab]
  apply hp.not_le_centralizer hcharI hIV
  rw [B6.conjSub_eq_self hgN]
  intro b hb
  exact Subgroup.mem_centralizer_iff.mpr fun v hv => hp.comm hv hb.2

end CFSG.Quasithin.SimsE2
