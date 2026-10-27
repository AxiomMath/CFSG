module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4S1B7

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.LieType.Ree
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem s1_commute_of_conj {g a b : G}
    (h : g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹)) : a * b = b * a := by
  have e1 : g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
  have e2 : g * b * g⁻¹ * (g * a * g⁻¹) = g * (b * a) * g⁻¹ := by group
  rw [e1, e2] at h
  simpa using h

private theorem s1_relIndex_ne_zero (H K : Subgroup G) : H.relIndex K ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

private theorem s1_relIndex_inf_left_of_le {H K X : Subgroup G} (h : H ≤ K) :
    (K ⊓ X).relIndex H = X.relIndex H := by
  have e := Subgroup.relIndex_inf_mul_relIndex (H := X) (K := K) (L := H)
  rw [inf_eq_right.mpr h, Subgroup.relIndex_eq_one.mpr h, mul_one, inf_comm] at e
  exact e.symm

section Step1

variable {L1 L2 S : Subgroup G} {a : ℕ}

theorem str83G4_s1_not_mem_normalizer
    (hfr : Str83G4Frame L1 L2 S a) {g : G} (hg : g ∈ L1 ⊔ S)
    (hc : ¬ Z2 L1 L2 S ≤ Subgroup.centralizer (CFSG.conjugate (Z2 L1 L2 S) g : Set G)) :
    g ∉ Subgroup.normalizer (S : Set G) := by
  intro hgS
  have h : g ∈ (L1 ⊔ S) ⊓ Subgroup.normalizer (Z2 L1 L2 S : Set G) := by
    rw [str83G4_normalizer_z2_eq hfr]
    exact ⟨hg, hgS⟩
  apply hc
  rw [CFSG.conjugate_eq_self_of_mem_normalizer h.2]
  exact fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
    A4.mul_comm_of_mem_omegaOneCenterOf hy hx

private theorem s1_facts
    (hfr : Str83G4Frame L1 L2 S a) {g : G} (hg : g ∈ L1 ⊔ S)
    (hc : ¬ Z2 L1 L2 S ≤ Subgroup.centralizer (CFSG.conjugate (Z2 L1 L2 S) g : Set G)) :
    CFSG.conjugate (Z2 L1 L2 S) g ⊔ Q2 L1 L2 S = S ∧
      Z2 L1 L2 S ⊓ Subgroup.centralizer (CFSG.conjugate (Z2 L1 L2 S) g : Set G) = Z1 L1 L2 S ∧
      Nat.card (Z2 L1 L2 S) = (2 ^ (2 * a + 1)) ^ 2 ∧
      CFSG.conjugate (Z2 L1 L2 S) g ⊓ Q2 L1 L2 S = Z1 L1 L2 S ∧
      (Q2 L1 L2 S ⊓ Subgroup.centralizer (CFSG.conjugate (Z2 L1 L2 S) g : Set G)) ⊔
          Z2 L1 L2 S = Q1 L1 L2 S ⊓ Q2 L1 L2 S := by
  classical
  have hfr' := hfr
  have hgN := str83G4_s1_not_mem_normalizer hfr hg hc
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨-, hZ1Z2, -, -, hZ2CS⟩ := str83_caseI_basics hF hB ha hSz hL2 hZI
  have hq : Nat.card (Z1 L1 L2 S) = 2 ^ (2 * a + 1) := str83G4Z1Card_holds G L1 L2 S a hfr'
  have hqpos : 0 < 2 ^ (2 * a + 1) := by positivity
  have hQ2S' : (Q2 L1 L2 S).relIndex S = 2 ^ (2 * a + 1) :=
    str86_relIndex_q2_s hF hB (by omega) hL2
  have hQ1S : Q1 L1 L2 S ≤ S := str83G4_q1_le_s hfr'
  have hQ2S : Q2 L1 L2 S ≤ S := str83G4_q2_le_s hfr'
  have hZ2Q1 : Z2 L1 L2 S ≤ Q1 L1 L2 S := (z2_le_str83X L1 L2 S).trans (str83X_le_q1 hfr')
  have hZ2Q2 : Z2 L1 L2 S ≤ Q2 L1 L2 S := Setup.omegaOneCenterOf_le _
  have hZ2ab : ∀ x ∈ Z2 L1 L2 S, ∀ y ∈ Z2 L1 L2 S, x * y = y * x := fun _ hx _ hy =>
    A4.mul_comm_of_mem_omegaOneCenterOf hx hy
  have hQ2C : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hSNZ2 : S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans (bigB_le_normalizer_z2 L1 L2 S)
  have hSNQ2 : S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S)).trans
      (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hgQ1 : g ∈ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    (sup_left_le_p1 L1 L2 S).trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S)) hg
  have hgZ1 : g ∈ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    (sup_left_le_p1 L1 L2 S).trans
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P1 L1 L2 S)) hg
  have hgq1 : ∀ y ∈ Q1 L1 L2 S, g * y * g⁻¹ ∈ Q1 L1 L2 S := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp hgQ1 y).mp hy
  have hcZ1 : CFSG.conjugate (Z1 L1 L2 S) g = Z1 L1 L2 S :=
    CFSG.conjugate_eq_self_of_mem_normalizer hgZ1
  have hB6 := str83G4_centralizer_conjugate_z2 hfr' hg
  have hB6i := str83G4_relIndex_q1_conjugate_q2 hfr' hg
  have hB6n := str83G4_normalizer_conjugate_z2 hfr' hg hgN
  obtain ⟨Zg, hZg⟩ : ∃ Zg : Subgroup G, Zg = CFSG.conjugate (Z2 L1 L2 S) g := ⟨_, rfl⟩
  rw [← hZg] at hc hB6 hB6n ⊢
  have hmemZg : ∀ y, y ∈ Zg ↔ g * y * g⁻¹ ∈ Z2 L1 L2 S := fun y => by
    rw [hZg]
    exact CFSG.mem_conjugate_iff _ _ _
  have hZgQ1 : Zg ≤ Q1 L1 L2 S := fun y hy => by
    have hgi : g⁻¹ ∈ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
      (Subgroup.normalizer (Q1 L1 L2 S : Set G)).inv_mem hgQ1
    have h := (Subgroup.mem_normalizer_iff.mp hgi (g * y * g⁻¹)).mp (hZ2Q1 ((hmemZg y).mp hy))
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rw [e] at h
    exact h
  have hZgS : Zg ≤ S := hZgQ1.trans hQ1S
  have hZ1Zg : Z1 L1 L2 S ≤ Zg := fun y hy => by
    rw [← hcZ1] at hy
    exact (hmemZg y).mpr (hZ1Z2 ((CFSG.mem_conjugate_iff _ _ _).mp hy))
  have hZgab : ∀ x ∈ Zg, ∀ y ∈ Zg, x * y = y * x := fun x hx y hy =>
    s1_commute_of_conj (g := g) (hZ2ab _ ((hmemZg x).mp hx) _ ((hmemZg y).mp hy))
  have hQ1NZg : Q1 L1 L2 S ≤ Subgroup.normalizer (Zg : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [hmemZg, hmemZg]
    have hy' : g * y * g⁻¹ ∈ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
      hSNZ2 (hQ1S (hgq1 y hy))
    have e : g * (y * w * y⁻¹) * g⁻¹ =
        g * y * g⁻¹ * (g * w * g⁻¹) * (g * y * g⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.mem_normalizer_iff.mp hy' _
  have hQ2gC : CFSG.conjugate (Q2 L1 L2 S) g ≤ Subgroup.centralizer (Zg : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact s1_commute_of_conj (g := g) ((Subgroup.mem_centralizer_iff.mp
      (hQ2C ((CFSG.mem_conjugate_iff _ _ _).mp hy))) _ ((hmemZg w).mp hw))
  obtain ⟨t, htZg, htQ2⟩ := SetLike.not_le_iff_exists.mp fun h : Zg ≤ Q2 L1 L2 S =>
    hc (Subgroup.le_centralizer_iff.mpr (h.trans hQ2C))
  obtain ⟨t', ht'Z2, ht'Q2⟩ :=
    SetLike.not_le_iff_exists.mp fun h : Z2 L1 L2 S ≤ CFSG.conjugate (Q2 L1 L2 S) g =>
      hc (h.trans hQ2gC)
  have hidx : ∀ x ∈ S, x ∉ Q2 L1 L2 S →
      (Subgroup.centralizer ({x} : Set G)).relIndex (Z2 L1 L2 S) = 2 ^ (2 * a + 1) := by
    intro x hx hxQ
    rw [← Subgroup.inf_relIndex_left,
      ← F53.Stellmacher.S43.card_commutator_zpowers hZ2ab (hSNZ2 hx),
      str83G4_commutator_z2_zpowers hfr' hx hxQ, hq]
  have hidx' : ∀ y ∈ Q1 L1 L2 S, y ∉ CFSG.conjugate (Q2 L1 L2 S) g →
      (Subgroup.centralizer ({y} : Set G)).relIndex Zg = 2 ^ (2 * a + 1) := by
    intro y hy hyQ
    have hx : g * y * g⁻¹ ∈ S := hQ1S (hgq1 y hy)
    have hxQ : g * y * g⁻¹ ∉ Q2 L1 L2 S := fun h =>
      hyQ ((CFSG.mem_conjugate_iff _ _ _).mpr h)
    have hcomm : ⁅Zg, Subgroup.zpowers y⁆ = Z1 L1 L2 S := by
      have h := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom)
        (str83G4_commutator_z2_zpowers hfr' hx hxQ)
      have hy' : (MulAut.conj g⁻¹).toMonoidHom (g * y * g⁻¹) = y := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [Subgroup.map_commutator, MonoidHom.map_zpowers, hy'] at h
      rw [hZg]
      exact h.trans hcZ1
    rw [← Subgroup.inf_relIndex_left,
      ← F53.Stellmacher.S43.card_commutator_zpowers hZgab (hQ1NZg hy), hcomm, hq]
  have hidxQ1 : (Subgroup.centralizer (Zg : Set G)).relIndex (Q1 L1 L2 S) =
      2 ^ (2 * a + 1) := by
    rw [← Subgroup.inf_relIndex_left, hB6, hB6i]
  have hZ2idx : (Subgroup.centralizer (Zg : Set G)).relIndex (Z2 L1 L2 S) =
      2 ^ (2 * a + 1) := by
    refine le_antisymm ((Subgroup.relIndex_le_of_le_right hZ2Q1
      (s1_relIndex_ne_zero _ _)).trans hidxQ1.le) ?_
    calc 2 ^ (2 * a + 1)
        = (Subgroup.centralizer ({t} : Set G)).relIndex (Z2 L1 L2 S) :=
          (hidx t (hZgS htZg) htQ2).symm
      _ ≤ (Subgroup.centralizer (Zg : Set G)).relIndex (Z2 L1 L2 S) :=
          Subgroup.relIndex_le_of_le_left
            (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htZg))
            (s1_relIndex_ne_zero _ _)
  have hQ2Zg : (Q2 L1 L2 S).relIndex Zg = 2 ^ (2 * a + 1) := by
    refine le_antisymm (hQ2S' ▸ Subgroup.relIndex_le_of_le_right hZgS
      (s1_relIndex_ne_zero _ _)) ?_
    calc 2 ^ (2 * a + 1)
        = (Subgroup.centralizer ({t'} : Set G)).relIndex Zg :=
          (hidx' t' (hZ2Q1 ht'Z2) ht'Q2).symm
      _ ≤ (Q2 L1 L2 S).relIndex Zg :=
          Subgroup.relIndex_le_of_le_left
            (hQ2C.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ht'Z2)))
            (s1_relIndex_ne_zero _ _)
  have hsup : Zg ⊔ Q2 L1 L2 S = S := by
    have h1 : (Q2 L1 L2 S).relIndex (Zg ⊔ Q2 L1 L2 S) = 2 ^ (2 * a + 1) := by
      rw [C5.relIndex_sup_eq_of_le_normalizer (hZgS.trans hSNQ2), hQ2Zg]
    have hle : Zg ⊔ Q2 L1 L2 S ≤ S := sup_le hZgS hQ2S
    have h2 := Subgroup.relIndex_mul_relIndex _ _ _
      (le_sup_right : Q2 L1 L2 S ≤ Zg ⊔ Q2 L1 L2 S) hle
    rw [h1, hQ2S'] at h2
    have h3 : (Zg ⊔ Q2 L1 L2 S).relIndex S = 1 :=
      Nat.eq_of_mul_eq_mul_left hqpos (h2.trans (mul_one _).symm)
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h3)
  have hZ1C : Z1 L1 L2 S ≤ Subgroup.centralizer (Zg : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hZgab y (hZ1Zg hy) x hx
  have hcent : Z2 L1 L2 S ⊓ Subgroup.centralizer (Zg : Set G) = Z1 L1 L2 S := by
    refine le_antisymm ?_ (le_inf hZ1Z2 hZ1C)
    have hCS : Subgroup.centralizer (S : Set G) =
        Subgroup.centralizer ((Zg ⊔ Q2 L1 L2 S : Subgroup G) : Set G) := by
      rw [hsup]
    have h : Z2 L1 L2 S ⊓ Subgroup.centralizer (Zg : Set G) ≤
        Subgroup.centralizer (S : Set G) := by
      rw [hCS]
      refine Subgroup.le_centralizer_iff.mpr
        (sup_le (Subgroup.le_centralizer_iff.mpr inf_le_right) ?_)
      exact hQ2C.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left))
    exact (le_inf inf_le_left h).trans hZ2CS.le
  have hcardZ2 : Nat.card (Z2 L1 L2 S) = (2 ^ (2 * a + 1)) ^ 2 := by
    have h := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (Zg : Set G))
      (K := Z2 L1 L2 S)
    rw [hZ2idx, inf_comm, hcent, hq] at h
    rw [sq]
    exact h.symm
  have hcardZg : Nat.card Zg = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [← hcardZ2, hZg]
    unfold CFSG.conjugate
    exact Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulEquiv.injective _)
  have hinf : Zg ⊓ Q2 L1 L2 S = Z1 L1 L2 S := by
    have h := Subgroup.relIndex_mul_card (H := Q2 L1 L2 S) (K := Zg)
    rw [hQ2Zg, hcardZg, inf_comm, sq] at h
    have h' : Nat.card (Zg ⊓ Q2 L1 L2 S : Subgroup G) = 2 ^ (2 * a + 1) :=
      Nat.eq_of_mul_eq_mul_left hqpos h
    exact (Subgroup.eq_of_le_of_card_ge (le_inf hZ1Zg (hZ1Z2.trans hZ2Q2))
      (h'.trans hq.symm).le).symm
  obtain ⟨C, hC⟩ : ∃ C : Subgroup G,
      C = Q2 L1 L2 S ⊓ Subgroup.centralizer (Zg : Set G) := ⟨_, rfl⟩
  rw [← hC]
  have hCQ1 : C ≤ Q1 L1 L2 S :=
    hC ▸ (inf_le_inf hQ2S (Subgroup.centralizer_le_normalizer _)).trans hB6n.le
  have hCQ2 : C ≤ Q2 L1 L2 S := hC ▸ inf_le_left
  have hmapsC : ∀ z ∈ Z2 L1 L2 S, ∀ y ∈ C, z * y * z⁻¹ ∈ C := by
    intro z hz y hy
    rw [hC] at hy ⊢
    obtain ⟨hyQ, hyC⟩ := Subgroup.mem_inf.mp hy
    have hzQ : z ∈ Q2 L1 L2 S := hZ2Q2 hz
    have hzN : z⁻¹ ∈ Subgroup.normalizer (Zg : Set G) :=
      (Subgroup.normalizer (Zg : Set G)).inv_mem (hQ1NZg (hZ2Q1 hz))
    refine Subgroup.mem_inf.mpr ⟨(Q2 L1 L2 S).mul_mem ((Q2 L1 L2 S).mul_mem hzQ hyQ)
      ((Q2 L1 L2 S).inv_mem hzQ), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : z⁻¹ * w * z⁻¹⁻¹ ∈ (Zg : Set G) := (Subgroup.mem_normalizer_iff.mp hzN w).mp hw
    have hcomm := Subgroup.mem_centralizer_iff.mp hyC _ hw'
    calc w * (z * y * z⁻¹) = z * ((z⁻¹ * w * z⁻¹⁻¹) * y) * z⁻¹ := by group
      _ = z * (y * (z⁻¹ * w * z⁻¹⁻¹)) * z⁻¹ := by rw [hcomm]
      _ = z * y * z⁻¹ * w := by group
  have hZ2NC : Z2 L1 L2 S ≤ Subgroup.normalizer (C : Set G) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hmapsC z hz y hy, fun hy => ?_⟩
    have h := hmapsC z⁻¹ ((Z2 L1 L2 S).inv_mem hz) _ hy
    have e : z⁻¹ * (z * y * z⁻¹) * z⁻¹⁻¹ = y := by group
    rw [e] at h
    exact h
  have hCZ2 : C ⊓ Z2 L1 L2 S = Z1 L1 L2 S := by
    rw [hC, inf_comm, ← inf_assoc, inf_eq_left.mpr hZ2Q2, hcent]
  have hidxC : C.relIndex (C ⊔ Z2 L1 L2 S) = 2 ^ (2 * a + 1) := by
    rw [sup_comm, C5.relIndex_sup_eq_of_le_normalizer hZ2NC, ← Subgroup.inf_relIndex_right, hCZ2,
      ← hcent, Subgroup.inf_relIndex_left, hZ2idx]
  have hle : C ⊔ Z2 L1 L2 S ≤ Q1 L1 L2 S ⊓ Q2 L1 L2 S :=
    sup_le (le_inf hCQ1 hCQ2) (le_inf hZ2Q1 hZ2Q2)
  have hCle : C.relIndex (Q1 L1 L2 S ⊓ Q2 L1 L2 S) ≤ 2 ^ (2 * a + 1) := by
    rw [hC, s1_relIndex_inf_left_of_le (inf_le_right : Q1 L1 L2 S ⊓ Q2 L1 L2 S ≤ Q2 L1 L2 S),
      ← hidxQ1]
    exact Subgroup.relIndex_le_of_le_right inf_le_left (s1_relIndex_ne_zero _ _)
  have h := Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_left : C ≤ C ⊔ Z2 L1 L2 S) hle
  rw [hidxC] at h
  have hx : (C ⊔ Z2 L1 L2 S).relIndex (Q1 L1 L2 S ⊓ Q2 L1 L2 S) = 1 := by
    have h1 : 2 ^ (2 * a + 1) * (C ⊔ Z2 L1 L2 S).relIndex (Q1 L1 L2 S ⊓ Q2 L1 L2 S) ≤
        2 ^ (2 * a + 1) * 1 := by
      rw [h, mul_one]
      exact hCle
    have h2 := Nat.le_of_mul_le_mul_left h1 hqpos
    have h3 := s1_relIndex_ne_zero (C ⊔ Z2 L1 L2 S) (Q1 L1 L2 S ⊓ Q2 L1 L2 S)
    omega
  exact ⟨hsup, hcent, hcardZ2, hinf, le_antisymm hle (Subgroup.relIndex_eq_one.mp hx)⟩

theorem str83G4_s1_sup_q2
    (hfr : Str83G4Frame L1 L2 S a) {g : G} (hg : g ∈ L1 ⊔ S)
    (hc : ¬ Z2 L1 L2 S ≤ Subgroup.centralizer (CFSG.conjugate (Z2 L1 L2 S) g : Set G)) :
    CFSG.conjugate (Z2 L1 L2 S) g ⊔ Q2 L1 L2 S = S :=
  (s1_facts hfr hg hc).1

theorem str83G4_s1_card_z2
    (hfr : Str83G4Frame L1 L2 S a) {g : G} (hg : g ∈ L1 ⊔ S)
    (hc : ¬ Z2 L1 L2 S ≤ Subgroup.centralizer (CFSG.conjugate (Z2 L1 L2 S) g : Set G)) :
    Nat.card (Z2 L1 L2 S) = (2 ^ (2 * a + 1)) ^ 2 :=
  (s1_facts hfr hg hc).2.2.1

theorem str83G4_s1_inf_q2
    (hfr : Str83G4Frame L1 L2 S a) {g : G} (hg : g ∈ L1 ⊔ S)
    (hc : ¬ Z2 L1 L2 S ≤ Subgroup.centralizer (CFSG.conjugate (Z2 L1 L2 S) g : Set G)) :
    CFSG.conjugate (Z2 L1 L2 S) g ⊓ Q2 L1 L2 S = Z1 L1 L2 S :=
  (s1_facts hfr hg hc).2.2.2.1

theorem str83G4_s1_centralizer_sup_z2
    (hfr : Str83G4Frame L1 L2 S a) {g : G} (hg : g ∈ L1 ⊔ S)
    (hc : ¬ Z2 L1 L2 S ≤ Subgroup.centralizer (CFSG.conjugate (Z2 L1 L2 S) g : Set G)) :
    (Q2 L1 L2 S ⊓ Subgroup.centralizer (CFSG.conjugate (Z2 L1 L2 S) g : Set G)) ⊔
        Z2 L1 L2 S = Q1 L1 L2 S ⊓ Q2 L1 L2 S :=
  (s1_facts hfr hg hc).2.2.2.2

end Step1

end CFSG.Quasithin.Stroth

end
