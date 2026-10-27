module

public import CFSG.Quasithin.Vol2.KGFactJ4Base
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocMain
public import CFSG.Sporadic.J4.QT2LocMain
public import CFSG.Sporadic.J4.QT2LocCntMain
public import CFSG.Sporadic.J4.QTRankInvProof

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

@[expose] def burnsideC31_J4NonParabolicTwoLocals : Prop :=
  ∀ P : Subgroup J, IsPGroup 2 ↥P → P ≠ ⊥ →
    (∀ g : J, ¬ P0.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (P : Set J)) →
    ∃ g : J,
      Subgroup.normalizer (P : Set J) ≤ Hj.map (MulAut.conj g).toMonoidHom ∨
      Subgroup.normalizer (P : Set J) ≤
        (Subgroup.centralizer ({CFSG.Quasithin.J4Loc.z0} : Set J)).map
          (MulAut.conj g).toMonoidHom ∨
      Subgroup.normalizer (P : Set J) ≤
        (Subgroup.normalizer (CFSG.Quasithin.J4Loc.V0 : Set J)).map
          (MulAut.conj g).toMonoidHom ∨
      Subgroup.normalizer (P : Set J) ≤ CFSG.Quasithin.KGJ4.M4.map (MulAut.conj g).toMonoidHom

theorem burnsideC31_conj_comp_conj_inv (g : J) :
    (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id J := by
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem burnsideC31_conj_inv_comp_conj (g : J) :
    (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id J := by
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem burnsideC31_kw_parabolic
    {P : Subgroup J} (hP : IsPGroup 2 ↥P) (hne : P ≠ ⊥) (g : J)
    (hg : P0.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (P : Set J)) :
    Subgroup.normalizer (P : Set J) ≤ Hj.map (MulAut.conj g).toMonoidHom ∨
      Subgroup.normalizer (P : Set J) ≤
        (Subgroup.centralizer ({CFSG.Quasithin.J4Loc.z0} : Set J)).map
          (MulAut.conj g).toMonoidHom ∨
      Subgroup.normalizer (P : Set J) ≤
        (Subgroup.normalizer (CFSG.Quasithin.J4Loc.V0 : Set J)).map
          (MulAut.conj g).toMonoidHom := by
  set P' : Subgroup J := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'def
  have hP' : IsPGroup 2 ↥P' := hP.map _
  have hne' : P' ≠ ⊥ := by
    intro h
    apply hne
    have h2 := congrArg (fun K : Subgroup J => K.map (MulAut.conj g).toMonoidHom) h
    simp only [hP'def, Subgroup.map_map, burnsideC31_conj_comp_conj_inv, Subgroup.map_id,
      Subgroup.map_bot] at h2
    exact h2
  have hN' : Subgroup.normalizer (P' : Set J) =
      (Subgroup.normalizer (P : Set J)).map (MulAut.conj g⁻¹).toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq P (MulAut.conj g⁻¹)).symm
  have hNP : Subgroup.normalizer (P : Set J) =
      (Subgroup.normalizer (P' : Set J)).map (MulAut.conj g).toMonoidHom := by
    rw [hN', Subgroup.map_map, burnsideC31_conj_comp_conj_inv, Subgroup.map_id]
  have hP0 : P0 ≤ Subgroup.normalizer (P' : Set J) := by
    rw [hN']
    have h1 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hg
    rwa [Subgroup.map_map, burnsideC31_conj_inv_comp_conj, Subgroup.map_id] at h1
  rw [hNP]
  rcases CFSG.Quasithin.J4Loc.j4TwoLocalOvergroups P' hP' hne' hP0 with h1 | h1 | h1
  · exact Or.inl (Subgroup.map_mono h1)
  · exact Or.inr (Or.inl (Subgroup.map_mono h1))
  · exact Or.inr (Or.inr (Subgroup.map_mono h1))

@[expose] def burnsideC31_J4KWCore : Prop :=
  ∀ A : Subgroup J, A ≠ ⊥ → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x * x = 1) →
    (∀ g : J, ¬ P0.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (A : Set J)) →
    (∀ a ∈ A, a ≠ 1 → ∃ n ∈ Subgroup.normalizer (A : Set J), n * a * n⁻¹ ≠ a) →
    ∃ g : J,
      Subgroup.normalizer (A : Set J) ≤ Hj.map (MulAut.conj g).toMonoidHom ∨
      Subgroup.normalizer (A : Set J) ≤
        (Subgroup.centralizer ({CFSG.Quasithin.J4Loc.z0} : Set J)).map
          (MulAut.conj g).toMonoidHom ∨
      Subgroup.normalizer (A : Set J) ≤
        (Subgroup.normalizer (CFSG.Quasithin.J4Loc.V0 : Set J)).map
          (MulAut.conj g).toMonoidHom ∨
      Subgroup.normalizer (A : Set J) ≤ CFSG.Quasithin.KGJ4.M4.map (MulAut.conj g).toMonoidHom

theorem burnsideC31_mem_map_centralizer {c y x : J}
    (hx : x ∈ Subgroup.centralizer ({c * y * c⁻¹} : Set J)) :
    c⁻¹ * x * c ∈ Subgroup.centralizer ({y} : Set J) ∧
      (MulAut.conj c).toMonoidHom (c⁻¹ * x * c) = x := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  refine ⟨?_, by simp [MulAut.conj_apply, mul_assoc]⟩
  have h2 : c⁻¹ * (x * (c * y * c⁻¹)) * c = c⁻¹ * ((c * y * c⁻¹) * x) * c := by rw [hx]
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, inv_mul_cancel,
    mul_one] using h2

theorem burnsideC31_centralizer_involution
    {a : J} (hsq : a * a = 1) (hne : a ≠ 1) :
    ∃ g : J, Subgroup.centralizer ({a} : Set J) ≤ Hj.map (MulAut.conj g).toMonoidHom ∨
      Subgroup.centralizer ({a} : Set J) ≤
        (Subgroup.centralizer ({CFSG.Quasithin.J4Loc.z0} : Set J)).map
          (MulAut.conj g).toMonoidHom := by
  rcases CFSG.Sporadic.J4.QT.inv_conj_root j4Facts hsq hne with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    refine ⟨c, Or.inl fun x hx => ?_⟩
    rw [← hc] at hx
    obtain ⟨h1, h2⟩ := burnsideC31_mem_map_centralizer hx
    refine ⟨c⁻¹ * x * c, ?_, h2⟩
    have h3 := Subgroup.mem_centralizer_singleton_iff.1 h1
    have h4 : (c⁻¹ * x * c) * eta uJ 11 1 = eta uJ 11 1 * (c⁻¹ * x * c) := h3
    exact CFSG.Sporadic.J4.QT2.centralizer_eta_one_le_Hj h4
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    obtain ⟨g, -, hg⟩ :=
      CFSG.Sporadic.J4.QT2.exists_conj_eta_three_of_mem_zMasks CFSG.Sporadic.J4.QT2.mem_zMasks_1131
    have hd : (c * g⁻¹) * CFSG.Quasithin.J4Loc.z0 * (c * g⁻¹)⁻¹ = a := by
      rw [← hc, CFSG.Quasithin.J4Loc.z0, ← hg]
      group
    refine ⟨c * g⁻¹, Or.inr fun x hx => ?_⟩
    rw [← hd] at hx
    obtain ⟨h1, h2⟩ := burnsideC31_mem_map_centralizer hx
    exact ⟨_, h1, h2⟩

theorem burnsideC31_normalizer_le_normalizer_omegaZ (P : Subgroup J) :
    Subgroup.normalizer (P : Set J) ≤
      Subgroup.normalizer (CFSG.Quasithin.J4Loc.omegaZ P : Set J) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => CFSG.Quasithin.J4Loc.omegaZ_conj hg hx
  · intro hx
    have hg' : g⁻¹ ∈ Subgroup.normalizer (P : Set J) :=
      (Subgroup.normalizer (P : Set J)).inv_mem hg
    have h1 := CFSG.Quasithin.J4Loc.omegaZ_conj hg' hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at h1

theorem burnsideC31_kw_of_core
    (h : burnsideC31_J4KWCore) : CFSG.Quasithin.KGJ4.J4TwoLocalsKW := by
  intro P hP hne
  set A := CFSG.Quasithin.J4Loc.omegaZ P with hAdef
  have hA : A ≠ ⊥ := CFSG.Quasithin.J4Loc.omegaZ_ne_bot hP hne
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hx.2.1 y hy.1
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => hx.2.2
  have hAp : IsPGroup 2 ↥A := hP.to_le (CFSG.Quasithin.J4Loc.omegaZ_le P)
  have hNA := burnsideC31_normalizer_le_normalizer_omegaZ P
  suffices key : ∃ g : J,
      Subgroup.normalizer (A : Set J) ≤ Hj.map (MulAut.conj g).toMonoidHom ∨
      Subgroup.normalizer (A : Set J) ≤
        (Subgroup.centralizer ({CFSG.Quasithin.J4Loc.z0} : Set J)).map
          (MulAut.conj g).toMonoidHom ∨
      Subgroup.normalizer (A : Set J) ≤
        (Subgroup.normalizer (CFSG.Quasithin.J4Loc.V0 : Set J)).map
          (MulAut.conj g).toMonoidHom ∨
      Subgroup.normalizer (A : Set J) ≤ CFSG.Quasithin.KGJ4.M4.map (MulAut.conj g).toMonoidHom by
    obtain ⟨g, h1 | h1 | h1 | h1⟩ := key
    · exact ⟨g, Or.inl (hNA.trans h1)⟩
    · exact ⟨g, Or.inr (Or.inl (hNA.trans h1))⟩
    · exact ⟨g, Or.inr (Or.inr (Or.inl (hNA.trans h1)))⟩
    · exact ⟨g, Or.inr (Or.inr (Or.inr (hNA.trans h1)))⟩
  by_cases hs : ∃ g : J, P0.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (A : Set J)
  · obtain ⟨g, hg⟩ := hs
    rcases burnsideC31_kw_parabolic hAp hA g hg with h1 | h1 | h1
    · exact ⟨g, Or.inl h1⟩
    · exact ⟨g, Or.inr (Or.inl h1)⟩
    · exact ⟨g, Or.inr (Or.inr (Or.inl h1))⟩
  by_cases hfix : ∃ a ∈ A, a ≠ 1 ∧ ∀ n ∈ Subgroup.normalizer (A : Set J), n * a * n⁻¹ = a
  · obtain ⟨a, haA, ha1, hfa⟩ := hfix
    have hNC : Subgroup.normalizer (A : Set J) ≤ Subgroup.centralizer ({a} : Set J) := by
      intro n hn
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e := hfa n hn
      calc n * a = n * a * n⁻¹ * n := by group
        _ = a * n := by rw [e]
    obtain ⟨g, h1 | h1⟩ := burnsideC31_centralizer_involution (hsq a haA) ha1
    · exact ⟨g, Or.inl (hNC.trans h1)⟩
    · exact ⟨g, Or.inr (Or.inl (hNC.trans h1))⟩
  · refine h A hA hcomm hsq (fun g hg => hs ⟨g, hg⟩) fun a ha ha1 => ?_
    by_contra hall
    push Not at hall
    exact hfix ⟨a, ha, ha1, hall⟩

end CFSG.ASVolI
