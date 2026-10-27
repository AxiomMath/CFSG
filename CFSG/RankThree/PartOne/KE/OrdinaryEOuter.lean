module

public import CFSG.LieType.Chevalley.OrdinaryEOuterOrder

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial (card_ringAut_and_isCyclic)

theorem le_center_of_normal_of_card_dvd_two {G : Type*} [Group G] (D : Subgroup G) [D.Normal]
    (h : Nat.card D ∣ 2) : D ≤ Subgroup.center G := by
  intro d hd
  rw [Subgroup.mem_center_iff]
  intro x
  by_cases hd1 : d = 1
  · subst hd1
    simp
  · have hcard : Nat.card D = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h2
      · exfalso
        apply hd1
        have := Subgroup.card_eq_one.1 h1
        rw [this] at hd
        simpa using hd
      · exact h2
    obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : D)).1 hcard
    have hd' : x * d * x⁻¹ ∈ D := ‹D.Normal›.conj_mem d hd x
    have e1 : (⟨d, hd⟩ : D) = y := huniq _ (by
      intro h
      exact hd1 (congrArg Subtype.val h))
    have e2 : (⟨x * d * x⁻¹, hd'⟩ : D) = y := huniq _ (by
      intro h
      apply hd1
      have h' : x * d * x⁻¹ = 1 := congrArg Subtype.val h
      rw [mul_inv_eq_one] at h'
      simpa using h')
    have e3 : x * d * x⁻¹ = d := congrArg Subtype.val (e2.trans e1.symm)
    rw [mul_inv_eq_iff_eq_mul] at e3
    exact e3

theorem commutator_le_ker_of_comm {G A : Type*} [Group G] [Group A] (Φ : G →* A)
    (hcomm : ∀ a b : A, a * b = b * a) : commutator G ≤ Φ.ker := by
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact Commute.commutator_eq (hcomm _ _)

theorem card_commutator_subgroup_dvd {G : Type*} [Group G] (H : Subgroup G) :
    Nat.card (commutator H) ∣ Nat.card (commutator G) := by
  have h1 : (commutator H).map H.subtype ≤ commutator G := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator]
    have : (⊤ : Subgroup H).map H.subtype = H := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [this]
    exact Subgroup.commutator_mono le_top le_top
  have h2 := Subgroup.card_dvd_of_le h1
  rwa [Subgroup.card_map_of_injective H.subtype_injective] at h2

theorem mul_comm_of_ker_le_center {G A : Type*} [Group G] [Group A] [IsCyclic A] (e : ℕ)
    (he : e = 1) (Φ : G →* A × Multiplicative (ZMod e)) (hD : Φ.ker ≤ Subgroup.center G)
    (x y : G) : x * y = y * x := by
  have hs : ∀ a b : Multiplicative (ZMod e), a = b := by
    have : Subsingleton (ZMod e) := ZMod.subsingleton_iff.2 he
    intro a b
    exact Subsingleton.elim (α := ZMod e) (Multiplicative.toAdd a) (Multiplicative.toAdd b)
  have hf : ((MonoidHom.fst A (Multiplicative (ZMod e))).comp Φ).ker ≤ Subgroup.center G := by
    intro x hx
    apply hD
    rw [MonoidHom.mem_ker]
    exact Prod.ext (MonoidHom.mem_ker.1 hx) (hs _ _)
  have := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center _ hf
  exact mul_comm' x y

theorem ordinary_E_outer_derived_subgroup_odd (τ : Tag)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : Type) [Field K] [Finite K] :
    ¬ 2 ∣ Nat.card (commutator (Outer (adjointGroup τ K))) ∧
      (τ = .E6 → Nat.card (commutator (Outer (adjointGroup τ K))) ∣ 3) ∧
      ((τ = .E7 ∨ τ = .E8) → ∀ x y : Outer (adjointGroup τ K), x * y = y * x) ∧
      ∀ H : Subgroup (Outer (adjointGroup τ K)), ¬ 2 ∣ Nat.card (commutator H) := by
  obtain ⟨Φ, -, -, hdvd⟩ := exists_outer_hom_E (K := K) hτ
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  obtain ⟨-, hcyc⟩ := card_ringAut_and_isCyclic hp K hK
  have hcomm : ∀ a b : RingAut K × Multiplicative (ZMod (exactE τ)), a * b = b * a := by
    intro a b
    refine Prod.ext ?_ ?_
    · exact mul_comm' a.1 b.1
    · exact mul_comm a.2 b.2
  have hcl : commutator (Outer (adjointGroup τ K)) ≤ Φ.ker := commutator_le_ker_of_comm Φ hcomm
  have hdvd' : Nat.card (commutator (Outer (adjointGroup τ K))) ∣ τ.cartan.det.natAbs :=
    (Subgroup.card_dvd_of_le hcl).trans hdvd
  have h6 : τ = .E6 → Nat.card (commutator (Outer (adjointGroup τ K))) ∣ 3 := by
    rintro rfl
    rw [det_cartan_E6] at hdvd'
    exact hdvd'
  have habel : (τ = .E7 ∨ τ = .E8) → ∀ x y : Outer (adjointGroup τ K), x * y = y * x := by
    intro h
    have he : exactE τ = 1 := by rcases h with rfl | rfl <;> rfl
    have hD2 : Nat.card Φ.ker ∣ 2 := by
      rcases h with rfl | rfl
      · rw [det_cartan_E7] at hdvd
        exact hdvd
      · rw [det_cartan_E8] at hdvd
        exact hdvd.trans (by decide)
    exact mul_comm_of_ker_le_center (exactE τ) he Φ
      (le_center_of_normal_of_card_dvd_two Φ.ker hD2)
  have hodd : ¬ 2 ∣ Nat.card (commutator (Outer (adjointGroup τ K))) := by
    rcases hτ with rfl | rfl | rfl
    · intro h2
      have h3 := h2.trans (h6 rfl)
      omega
    · have hc : commutator (Outer (adjointGroup .E7 K)) = ⊥ :=
        (commutator_eq_bot_iff_center_eq_top _).2 ((Subgroup.eq_top_iff' _).2 fun x =>
          Subgroup.mem_center_iff.2 fun g => habel (Or.inl rfl) g x)
      rw [hc, Subgroup.card_bot]
      omega
    · have hc : commutator (Outer (adjointGroup .E8 K)) = ⊥ :=
        (commutator_eq_bot_iff_center_eq_top _).2 ((Subgroup.eq_top_iff' _).2 fun x =>
          Subgroup.mem_center_iff.2 fun g => habel (Or.inr rfl) g x)
      rw [hc, Subgroup.card_bot]
      omega
  refine ⟨hodd, h6, habel, fun H h2 => hodd ?_⟩
  exact h2.trans (card_commutator_subgroup_dvd H)

end CFSG.RankThree.PartOne.KE
