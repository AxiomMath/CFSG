module

public import CFSG.Quasithin.EmptyFaithful.S153G27
public import CFSG.Quasithin.EmptyFaithful.SBdQuasi

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBd

theorem exists_center_orderOf_three_SL3 {K : Type} [Field K] [Finite K] {n : ℕ} (hn : Even n)
    (hK : Nat.card K = 2 ^ n) :
    ∃ w ∈ Subgroup.center ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K), orderOf w = 3 := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have h := Nat.pow_sub_one_dvd_pow_sub_one (x := 2) (even_iff_two_dvd.mp hn)
    simpa using h
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hω
    omega
  set s : GL (Fin 3) K := Matrix.GeneralLinearGroup.scalar (Fin 3) ω with hs
  have hdet : (s : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have h1 : (ω : K) ^ 3 = 1 := by simpa using congrArg Units.val hω3
    simpa [hs] using h1
  have hmem : s ∈ CFSG.Assembly.LowTwoRank.StatedSL 3 K := Subgroup.subset_closure hdet
  have hcent : s ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨ω, rfl⟩
  have hs3 : s ^ 3 = 1 := by rw [hs, ← map_pow, hω3, map_one]
  have hs1 : s ≠ 1 := by
    intro h1
    apply hω1
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp [hs] at this
    ext
    simpa using this
  refine ⟨⟨s, hmem⟩, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hcent (g : GL (Fin 3) K))
  · refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext hs3
    · intro h
      exact hs1 (congrArg Subtype.val h)

theorem three_dvd_card_center {X : Type} [Group X] [Finite X]
    (h : (∃ n : ℕ, Even n ∧ IsSL3 (2 ^ n) X) ∨ IsHat X (alternatingGroup (Fin 6))) :
    3 ∣ Nat.card ↥(Subgroup.center X) := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases h with ⟨n, hn, K, hKf, hKfin, hK, ⟨e⟩⟩ | hHat
  · let := hKf
    have := hKfin
    obtain ⟨w, hw, hw3⟩ := exists_center_orderOf_three_SL3 hn hK
    have hz : e.symm w ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_center_iff.mp hw (e g)
    have h1 := orderOf_dvd_natCard (⟨e.symm w, hz⟩ : ↥(Subgroup.center X))
    rwa [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, hw3] at h1
  · rw [hHat.2.1]

theorem le_Yp_of_forall_orderOf_three_pow {G : Type} [Group G] [Finite G]
    {T Mc M V₁ V₂ Yp I : Subgroup G} (hF : Facts15325 T Mc M V₁ V₂ Yp I) {Q : Subgroup G}
    (hQ : Q ≤ M ⊓ I) (hQp : IsPGroup 3 ↥Q) : Q ≤ Yp := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hx
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hQp) ⟨x, hx⟩
  rw [hF.yp_eq]
  exact Subgroup.subset_closure ⟨hQ hx, j, by rw [← hj]; exact (Subgroup.orderOf_mk x hx).symm⟩

theorem not_nine_dvd_card_MI {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I : Subgroup G}
    (hF : Facts15325 T Mc M V₁ V₂ Yp I) : ¬ 9 ∣ Nat.card ↥(M ⊓ I) := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h9
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(M ⊓ I)) 3 (n := 2) (by simpa using h9)
  have hQp : IsPGroup 3 ↥(Q.map (M ⊓ I).subtype) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Subgroup.card_map_of_injective (M ⊓ I).subtype_injective, hQ]
  have hle : Q.map (M ⊓ I).subtype ≤ Yp :=
    le_Yp_of_forall_orderOf_three_pow hF (by rintro _ ⟨q, -, rfl⟩; exact q.2) hQp
  have h1 : Nat.card ↥(Q.map (M ⊓ I).subtype) ∣ Nat.card Yp := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective (M ⊓ I).subtype_injective, hQ] at h1
  exact not_nine_dvd_card_Yp hF (by simpa using h1)

theorem input27Center_proved : Input27Center := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hN hcase
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF : Facts15325 T Mc M V₁ V₂ Yp I := c.facts
  obtain ⟨hLc, hLn, hL3, hLY, hLq, hLq2⟩ := c.conc
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hUN : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hLU : L ≤ Subgroup.normalizer (UI153 T I : Set G) := hLle.trans hUN
  have hRL : solvRad L ≤ L := solvRad_le L
  have hIR : I ≤ Subgroup.normalizer (solvRad L : Set G) :=
    hN.trans (normalizer_le_normalizer_solvRad L)
  have hRM : solvRad L ≤ M ⊓ I :=
    c.solv (solvRad L) (hRL.trans hLle) (solvRad_isSolvable L) (c.ctx.inH.1.1.trans hIR)
  have hZ : 3 ∣ Nat.card ↥(Subgroup.center ↥(autOn L (UI153 T I))) :=
    three_dvd_card_center (X := ↥(Star153 T I L)) hcase
  have h3R : 3 ∣ Nat.card ↥(solvRad L) := by
    obtain ⟨z', hz'⟩ := exists_prime_orderOf_dvd_card' 3 hZ
    obtain ⟨l, hl⟩ := S153D.autOnHom_surjective hLU (z' : ↥(autOn L (UI153 T I)))
    let P : Subgroup ↥L := (Subgroup.center ↥(autOn L (UI153 T I))).comap (S153D.autOnHom hLU)
    have hPtop : P ≠ ⊤ := by
      intro hP
      have hcomm : ∀ a b : ↥(autOn L (UI153 T I)), a * b = b * a := by
        intro a b
        obtain ⟨l', rfl⟩ := S153D.autOnHom_surjective hLU a
        have : l' ∈ P := hP ▸ Subgroup.mem_top l'
        exact (Subgroup.mem_center_iff.mp this b).symm
      exact S153D.not_isSolvable_of_isQuasisimple hLq (Group.isSolvable_of_comm hcomm)
    have hPR : P.map L.subtype ≤ solvRad L :=
      (normal_eq_top_or_map_le_solvRad hLI P).resolve_left hPtop
    have hlR : (l : G) ∈ solvRad L :=
      hPR ⟨l, by simp [P, hl], rfl⟩
    let φR : ↥(solvRad L) →* ↥(autOn L (UI153 T I)) :=
      (S153D.autOnHom hLU).comp (Subgroup.inclusion hRL)
    have h1 : orderOf (φR ⟨l, hlR⟩) ∣ orderOf (⟨l, hlR⟩ : ↥(solvRad L)) := orderOf_map_dvd φR _
    have h2 : φR ⟨l, hlR⟩ = (z' : ↥(autOn L (UI153 T I))) := hl
    rw [h2, Subgroup.orderOf_coe, hz'] at h1
    exact h1.trans (orderOf_dvd_natCard _)
  have hMIN : M ⊓ I ≤ Subgroup.normalizer (solvRad L : Set G) := inf_le_right.trans hIR
  have hYR : Yp ≤ solvRad L := by
    have hall : ∀ x : G, x ∈ M ⊓ I → (∃ j : ℕ, orderOf x = 3 ^ j) → x ∈ solvRad L :=
      fun x hx hj => mem_of_orderOf_three_pow hRM hMIN h3R (not_nine_dvd_card_MI hF) hx hj
    rw [hF.yp_eq]
    exact (Subgroup.closure_le _).mpr fun x hx => hall x hx.1 hx.2
  have hLR : ⁅L, Yp⁆ ≤ L ⊓ Subgroup.centralizer (UI153 T I : Set G) :=
    (Subgroup.commutator_mono le_rfl hYR).trans (commutator_solvRad_le hLI hLU hLq)
  rw [hLY] at hLR
  have hbot : autOn L (UI153 T I) = ⊥ := (autOn_eq_bot_iff hLU).mpr (hLR.trans inf_le_right)
  have hnt : Nontrivial ↥(autOn L (UI153 T I)) := CFSG.LocalCores.isQuasisimple_nontrivial hLq
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥(autOn L (UI153 T I)))
  apply ha
  have : (a : MulAut ↥(UI153 T I)) ∈ (⊥ : Subgroup (MulAut ↥(UI153 T I))) := hbot ▸ a.2
  exact Subtype.ext (Subgroup.mem_bot.mp this)

end SBd

end CFSG.Quasithin
