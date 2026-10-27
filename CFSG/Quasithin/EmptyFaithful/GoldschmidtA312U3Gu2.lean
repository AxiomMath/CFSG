module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Dick
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin.A38c15 CFSG.RankThree.SubgroupLists CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]

open CFSG.GH74.GLS.IVK.Proofs2 in
omit [Finite F] in
theorem scalar_pow_eq_one (hF : Nat.card F = p ^ 2) {c : Fˣ}
    (hc : Matrix.GeneralLinearGroup.scalar (Fin 2) c ∈ GU2Stated (p ^ 1) F) : c ^ (p + 1) = 1 := by
  have hU := uniData (p := p) hF
  have h1 := (Lemma41aU3.mem_GU2Stated_iff hU).mp hc
  have h2 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) h1
  simp [Matrix.mul_apply, Fin.sum_univ_two, hU.bar_apply] at h2
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, pow_succ, Units.val_one]
  simpa [mul_comm] using h2

open CFSG.GH74.GLS.IVK.Proofs2 in
theorem card_inf_center_dvd (hF : Nat.card F = p ^ 2) {H : Subgroup (GL (Fin 2) F)}
    (hH : H ≤ GU2Stated (p ^ 1) F) :
    Nat.card ↥(H ⊓ Subgroup.center (GL (Fin 2) F)) ∣ p + 1 := by
  classical
  let sc : Fˣ →* GL (Fin 2) F := Matrix.GeneralLinearGroup.scalar (Fin 2)
  have hinj : Function.Injective sc := fun a b hab => by
    have := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 0 0) hab
    exact Units.ext (by simpa [sc] using this)
  let D : Subgroup Fˣ := H.comap sc
  have hD : H ⊓ Subgroup.center (GL (Fin 2) F) = D.map sc := by
    ext x
    rw [Subgroup.mem_inf, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    constructor
    · rintro ⟨hx, c, rfl⟩
      exact ⟨c, hx, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨hc, c, rfl⟩
  have hDle : D ≤ rootsOfUnity (p + 1) F := fun c hc =>
    (mem_rootsOfUnity _ _).mpr (scalar_pow_eq_one hF (hH hc))
  have hq : Nat.card (rootsOfUnity (p + 1) F) = p + 1 := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd, hF]
    refine Nat.gcd_eq_right ?_
    refine ⟨p - 1, ?_⟩
    have hp1 : 1 ≤ p := Fact.out (p := p.Prime) |>.one_lt.le
    zify [hp1, show 1 ≤ p ^ 2 from Nat.one_le_pow _ _ (by omega)]
    ring
  rw [hD, Subgroup.card_map_of_injective hinj, ← hq]
  exact Subgroup.card_dvd_of_le hDle

theorem eight_dvd_of_dvd_mul {k r n : ℕ} (hk : k ∣ n) (hn : n ≠ 0) (hk0 : k ≠ 0) (hr : r ≠ 0)
    (hdiv : 2 ^ (3 + n.factorization 2) ∣ k * r) : 8 ∣ r := by
  have h2 : 3 + n.factorization 2 ≤ (k * r).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (mul_ne_zero hk0 hr)).mp hdiv
  rw [Nat.factorization_mul hk0 hr, Finsupp.add_apply] at h2
  have h3 : k.factorization 2 ≤ n.factorization 2 :=
    (Nat.factorization_le_iff_dvd hk0 hn).mpr hk 2
  have h4 : 3 ≤ r.factorization 2 := by omega
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hr).mpr h4
  simpa using this

open CFSG.GH74.GLS.IVK.Proofs2 in
theorem gu2_core (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2)
    {H : Subgroup (GL (Fin 2) F)} (hH : H ≤ GU2Stated (p ^ 1) F)
    (h8 : 2 ^ (3 + (p + 1).factorization 2) ∣ Nat.card H) :
    Group.IsSolvable ↥H ∨ Nonempty (↥(perfectCore H) ≃* SL(2, ZMod p)) := by
  classical
  by_cases hs : Group.IsSolvable ↥H
  · exact Or.inl hs
  right
  have hU := uniData (p := p) hF
  have h2 := two_ne_zero_of_card_sq (p := p) hp2 hF
  have hcp := charP_of_card_sq (p := p) hF
  set Q : Subgroup (GL (Fin 2) F) := perfectCore H with hQdef
  have hQperf : ⁅Q, Q⁆ = Q := perfectCore_perfect H
  have hQH : Q ≤ H := perfectCore_le H
  have hQne : Q ≠ ⊥ := fun h => hs ((isSolvable_iff_perfectCore_eq_bot H).mpr h)
  have : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.mpr hQperf
  have hdet : ∀ y ∈ Q, (y : Matrix (Fin 2) (Fin 2) F).det = 1 := fun y hy =>
    CFSG.SectionRank.Ccomm.det_eq_one_of_perfect Q hy
  have hQsu : Q ≤ StatedSU 2 (p ^ 1) F := fun y hy =>
    (mem_unitarySU_iff hU).mpr
      ⟨hdet y hy, (Lemma41aU3.mem_GU2Stated_iff hU).mp (hH (hQH hy))⟩
  rcases dickson_su2 hp2 hF hQsu hQne with hSL | ⟨h5, hcen, ⟨φ⟩⟩
  · exact hSL
  · exfalso
    have hnorm : ∀ g ∈ H, ∃ y ∈ Q, ∃ c : F, (g : Matrix (Fin 2) (Fin 2) F) =
        (y : Matrix (Fin 2) (Fin 2) F) * Matrix.scalar (Fin 2) c := by
      intro g' hg'
      refine exists_eq_mul_scalar_of_normalizes_sl25 h2 h5 Q hQperf hdet hcen φ ?_ ?_
      · intro x hx
        exact (perfectCore_normal H).conj_mem ⟨x, hQH hx⟩ hx ⟨g', hg'⟩
      · intro x hx
        have := (perfectCore_normal H).conj_mem ⟨x, hQH hx⟩ hx ⟨g'⁻¹, H.inv_mem hg'⟩
        rw [Subgroup.mem_subgroupOf] at this
        simpa using this
    let π : GL (Fin 2) F →* Matrix.ProjGenLinGroup (Fin 2) F := Matrix.ProjGenLinGroup.mk
    have hπH : H.map π ≤ Q.map π := by
      rintro _ ⟨g', hg', rfl⟩
      obtain ⟨y, hy, c, hc⟩ := hnorm g' hg'
      refine ⟨y, hy, ?_⟩
      have hz : (y : GL (Fin 2) F)⁻¹ * g' ∈ Subgroup.center (GL (Fin 2) F) := by
        rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
        refine ⟨c, ?_⟩
        rw [Units.val_mul, hc, ← mul_assoc, Units.inv_mul, one_mul]
      have h1 : π ((y : GL (Fin 2) F)⁻¹ * g') = 1 :=
        Matrix.ProjGenLinGroup.mk_eq_one.mpr hz
      rw [map_mul, map_inv] at h1
      exact inv_mul_eq_one.mp h1
    have hcard : Nat.card (↥Q ⧸ Subgroup.center ↥Q) = 60 := by
      rw [Nat.card_congr φ.toEquiv, card_alt_five_fin]
    have hQ60 : Nat.card (Q.map π) ∣ 60 := by
      let ψ : ↥Q →* Matrix.ProjGenLinGroup (Fin 2) F := π.comp Q.subtype
      have hψ1 : ∀ z ∈ Subgroup.center ↥Q, ψ z = 1 := by
        intro z hz
        have hz' := (hcen z).mp hz
        show π (z : GL (Fin 2) F) = 1
        rcases hz' with h | h
        · rw [h, map_one]
        · rw [h]
          refine Matrix.ProjGenLinGroup.mk_eq_one.mpr ?_
          rw [Subgroup.mem_center_iff]
          intro x
          simp
      let ψr : ↥Q →* ψ.range := ψ.rangeRestrict
      have hψr : ∀ z ∈ Subgroup.center ↥Q, ψr z = 1 := fun z hz => Subtype.ext (hψ1 z hz)
      let ψ' : (↥Q ⧸ Subgroup.center ↥Q) →* ψ.range :=
        QuotientGroup.lift (Subgroup.center ↥Q) ψr hψr
      have hsurj : Function.Surjective ψ' := by
        intro r
        obtain ⟨q, hq⟩ := ψ.rangeRestrict_surjective r
        exact ⟨QuotientGroup.mk q, hq⟩
      have hdvd : Nat.card ψ.range ∣ Nat.card (↥Q ⧸ Subgroup.center ↥Q) :=
        Subgroup.card_dvd_of_surjective hsurj
      have hrange : ψ.range = Q.map π := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [hrange, hcard] at hdvd
      exact hdvd
    have h8π : 8 ∣ Nat.card (H.map π) := by
      let ψ : ↥H →* Matrix.ProjGenLinGroup (Fin 2) F := π.comp H.subtype
      have hkerπ : π.ker = Subgroup.center (GL (Fin 2) F) := by
        ext x
        rw [MonoidHom.mem_ker]
        exact Matrix.ProjGenLinGroup.mk_eq_one
      have hker : Nat.card ψ.ker ∣ p + 1 := by
        have hk1 : ψ.ker = (π.ker).subgroupOf H := rfl
        have hk2 : Nat.card ψ.ker = Nat.card ↥(H ⊓ Subgroup.center (GL (Fin 2) F)) := by
          rw [hk1, ← Subgroup.card_map_of_injective H.subtype_injective,
            Subgroup.subgroupOf_map_subtype, hkerπ, inf_comm]
        rw [hk2]
        exact card_inf_center_dvd hF hH
      have hrange : ψ.range = H.map π := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      have hcardH := Subgroup.card_ker_mul_card_range ψ
      rw [hrange] at hcardH
      have hdiv : 2 ^ (3 + (p + 1).factorization 2) ∣ Nat.card ψ.ker * Nat.card (H.map π) := by
        rw [hcardH]
        exact h8
      exact eight_dvd_of_dvd_mul hker (Nat.succ_ne_zero p) Nat.card_pos.ne' Nat.card_pos.ne' hdiv
    have := (h8π.trans (Subgroup.card_dvd_of_le hπH)).trans hQ60
    omega

end CFSG.Quasithin.A312U3
