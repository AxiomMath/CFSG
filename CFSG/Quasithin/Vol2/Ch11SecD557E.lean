module

public import CFSG.Quasithin.Vol2.Ch11SecD557D
public import CFSG.Quasithin.Vol2.Ch11SecD557B
public import CFSG.Quasithin.Vol2.Ch11SecD557C

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Quasithin.SL3Model
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem coprime_card_of_odd {X P : Subgroup G} (hX : Odd (Nat.card X)) (hP : IsPGroup 2 P) :
    Nat.Coprime (Nat.card X) (Nat.card P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  rw [hk]
  exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hX)

theorem isSolvable_of_isPGroup_two {P : Subgroup G} (hP : IsPGroup 2 P) :
    Group.IsSolvable ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hP.isNilpotent
  infer_instance

omit [Finite G] in
theorem S₃_le (S : Subgroup G) (Uk : Fin 3 → Subgroup G) : TripleGrp.S₃ S Uk ≤ S :=
  sup_le (sup_le (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_right))
    (inf_le_left.trans inf_le_right)

variable {n : ℕ} {V V₁ L T H : Subgroup G} (St : L3Setting n V V₁ L T H) {g h : G}

include St in
theorem mem_S₂_of_forall_conj_eq (hg : g ∈ L) (hh : h ∈ L) (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h)
    {X : Subgroup G} (hXL : X ≤ L) (hXodd : Odd (Nat.card X))
    (hfix : V ⊓ Subgroup.centralizer (X : Set G) = ⊥) {z : G}
    (hz : z ∈ pCoreOf 2 (L ⊔ conjClosure V H)) (hzX : ∀ a ∈ X, a * z * a⁻¹ = z) :
    z ∈ TripleGrp.S₂ (tripleU (conjClosure V H) g h) := by
  obtain ⟨r, s, φ₇, φ₆, h7, -, h6, -, -⟩ := St.G25_fam hg hh hV
  have hXI : X ≤ L ⊔ conjClosure V H := hXL.trans le_sup_left
  let Xs : Set ↥(L ⊔ conjClosure V H) := {a | (a : G) ∈ X}
  have hPhi : ∀ a : ↥X, St.Phi ⟨a, hXI a.2⟩ = St.D.θ ⟨a, hXL a.2⟩ := fun a =>
    St.Phi_of_L ⟨a, hXL a.2⟩
  have hfix₇ : ∀ v : Fin 3 → GaloisField 2 n, (∀ a ∈ Xs, St.Phi a • v = v) → v = 0 :=
    fun v hv => fix_eq_zero_of_inf_centralizer St.D hXL hfix v fun a => by
      rw [← hPhi a]
      exact hv ⟨a, hXI a.2⟩ a.2
  let Hx : Subgroup SL(3, GaloisField 2 n) := (X.subgroupOf (L ⊔ conjClosure V H)).map St.Phi
  have hHodd : Odd (Nat.card Hx) := by
    have h1 : Nat.card Hx ∣ Nat.card ↥(X.subgroupOf (L ⊔ conjClosure V H)) :=
      Subgroup.card_map_dvd _ St.Phi
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXI).toEquiv] at h1
    exact Odd.of_dvd_nat hXodd h1
  have hfixH : ∀ v : Fin 3 → GaloisField 2 n, (∀ A ∈ Hx, A • v = v) → v = 0 := fun v hv =>
    hfix₇ v fun a ha => hv _ ⟨a, ha, rfl⟩
  have hfix₆ : ∀ f : Fin 3 → GaloisField 2 n,
      (∀ a ∈ Xs, ((dualHom (GaloisField 2 n) 3).comp St.Phi) a • f = f) → f = 0 := by
    intro f hf
    refine dual_fix_eq_zero Hx hHodd hfixH f fun A hA => ?_
    obtain ⟨a, ha, rfl⟩ := hA
    exact hf a ha
  have hz₃ := mem_of_forall_conj_eq h7 Xs hfix₇ ⟨z, hz⟩ fun a ha => hzX a ha
  exact mem_of_forall_conj_eq h6 Xs hfix₆ ⟨z, hz₃⟩ fun a ha => hzX a ha

include St in
theorem le_commutator_sup_S₃ (hg : g ∈ L) (hh : h ∈ L) (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h)
    {A : Subgroup G} (hAL : A ≤ L) (hcomm : ⁅V, A⁆ = V) :
    pCoreOf 2 (L ⊔ conjClosure V H) ≤ ⁅pCoreOf 2 (L ⊔ conjClosure V H), A⁆ ⊔
      TripleGrp.S₃ (pCoreOf 2 (L ⊔ conjClosure V H)) (tripleU (conjClosure V H) g h) := by
  obtain ⟨r, s, φ₇, φ₆, h7, -, -, -, -⟩ := St.G25_fam hg hh hV
  obtain ⟨-, -, -, hInorm, -⟩ := St.sxFacts
  have hAI : A ≤ L ⊔ conjClosure V H := hAL.trans le_sup_left
  have hP : ∀ a : ↥A, St.Phi ⟨a, hAI a.2⟩ = St.D.θ ⟨a, hAL a.2⟩ := fun a =>
    St.Phi_of_L ⟨a, hAL a.2⟩
  refine le_commutator_sup_of_span h7 hAI (fun a ha z hz => hInorm a (hAI ha) z hz) fun w => ?_
  have hset : {u | ∃ v : Fin 3 → GaloisField 2 n, ∃ a : ↥A, u = v - St.Phi ⟨a, hAI a.2⟩ • v} =
      {u | ∃ v : Fin 3 → GaloisField 2 n, ∃ a : ↥A, u = v - St.D.θ ⟨a, hAL a.2⟩ • v} := by
    ext u
    exact ⟨fun ⟨v, a, hu⟩ => ⟨v, a, by rw [hu, hP a]⟩,
      fun ⟨v, a, hu⟩ => ⟨v, a, by rw [hu, hP a]⟩⟩
  rw [hset]
  exact span_of_commutator_eq St.D hAL hcomm w

include St in
theorem frattini_le_S₂ (hg : g ∈ L) (hh : h ∈ L) (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h)
    {P : Subgroup G}
    (hP : P ≤ TripleGrp.S₃ (pCoreOf 2 (L ⊔ conjClosure V H)) (tripleU (conjClosure V H) g h)) :
    (frattini P).map P.subtype ≤ TripleGrp.S₂ (tripleU (conjClosure V H) g h) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, s, φ₇, φ₆, -, -, h6, -, -⟩ := St.G25_fam hg hh hV
  have hP2 : IsPGroup 2 P :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le (hP.trans (S₃_le _ _))
  exact frattini_map_le_of_forall' hP2
    (fun a ha b hb => commutator_mem_of_ker h6.2.1 (hP ha) (hP hb))
    (fun a ha => sq_mem_of_ker h6.2.1 (hP ha))

include St in
theorem le_S₂_of_comm (hg : g ∈ L) (hh : h ∈ L) (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h)
    (hcomm : ∀ u ∈ conjClosure V H, ∀ z ∈ pCoreOf 2 (L ⊔ conjClosure V H),
      u * z * u⁻¹ * z⁻¹ ∈ V₁) :
    pCoreOf 2 (L ⊔ conjClosure V H) ≤ TripleGrp.S₂ (tripleU (conjClosure V H) g h) := by
  obtain ⟨r, s, φ₇, φ₆, h7, -, h6, -, -⟩ := St.G25_fam hg hh hV
  obtain ⟨-, -, -, hInorm, -⟩ := St.sxFacts
  have htg := St.tripleGrp hg hh hV
  have h4 := St.G25_four_inv hg hh hV
  obtain ⟨u, huU, huO⟩ := IsConcreteLE.not_le_iff_exists.mp St.hyp.U_ne
  have huI : u ∈ L ⊔ conjClosure V H := (le_sup_right : conjClosure V H ≤ _) huU
  have hPhi : St.Phi ⟨u, huI⟩ ≠ 1 := fun h1 => huO ((St.Phi_eq_one_iff _).mp h1)
  have hVU : ∀ k, V ≤ tripleU (conjClosure V H) g h k := fun k =>
    St.V_le_rconj_U (tripleConj_mem hg hh k)
  have hV₁S₂ : V₁ ≤ TripleGrp.S₂ (tripleU (conjClosure V H) g h) :=
    St.hyp.base.le_V.trans (le_inf (le_inf (hVU 0) (hVU 1)) (hVU 2))
  have hS₂S₃ : TripleGrp.S₂ (tripleU (conjClosure V H) g h) ≤
      TripleGrp.S₃ (pCoreOf 2 (L ⊔ conjClosure V H)) (tripleU (conjClosure V H) g h) :=
    (le_inf (htg.S₂_le_W 0) (htg.S₂_le_W 1)).trans (le_sup_left.trans le_sup_left)
  have hr : r = 0 := eq_zero_of_isSumOfSL3ModulesVia h7 ⟨u, huI⟩
    (fun z hz => hInorm u huI z hz) (fun z hz => hS₂S₃ (hV₁S₂ (hcomm u huU z hz))) hPhi
  have hs : s = 0 := by
    refine eq_zero_of_isSumOfSL3ModulesVia h6 ⟨u, huI⟩
      (fun z hz => (Subgroup.mem_normalizer_iff.mp (h4 huI) z).mp hz)
      (fun z hz => hV₁S₂ (hcomm u huU z (S₃_le _ _ hz))) fun h1 => hPhi ?_
    rw [← dualHom_dualHom (St.Phi ⟨u, huI⟩)]
    rw [MonoidHom.comp_apply] at h1
    rw [h1, map_one]
  subst hr
  subst hs
  intro z hz
  have hz3 := (h7.2.1 ⟨z, hz⟩).mp (Subsingleton.elim _ _)
  exact (h6.2.1 ⟨z, hz3⟩).mp (Subsingleton.elim _ _)

end CFSG.Quasithin.Vol2.Ch11.SecD
