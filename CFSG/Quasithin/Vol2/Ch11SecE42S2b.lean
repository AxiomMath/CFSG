module

public import CFSG.Quasithin.Vol2.Ch11SecE43Out
public import CFSG.Quasithin.Vol2.Ch11SecA11Setup
public import CFSG.Quasithin.Vol2.Ch11SecE42Rad
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem rOf_le_T (h : Hyp11 G T L I n) (V₁ : Subgroup G) : ROf T L V₁ ≤ T := by
  have hsyl := isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow (le_sup_right : T ≤ LOf L V₁ ⊔ T)
  exact pCoreOf_two_le_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2

theorem rOf_le_normalizer_lOf (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) : ROf T L V₁ ≤ Subgroup.normalizer (LOf L V₁ : Set G) :=
  (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le Subgroup.le_normalizer
    (SecA.T_le_normalizer_lOf h.normal (SecA.IsVi.le_normalizer hV₁)))

omit [Finite G] in
theorem lOf_le_normalizer_rOf (T L V₁ : Subgroup G) :
    LOf L V₁ ≤ Subgroup.normalizer (ROf T L V₁ : Set G) :=
  le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)

omit [Finite G] in
theorem T_le_normalizer_rOf (T L V₁ : Subgroup G) :
    T ≤ Subgroup.normalizer (ROf T L V₁ : Set G) :=
  le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)

theorem commutator_rOf_lOf_le (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) : ⁅ROf T L V₁, LOf L V₁⁆ ≤ pCoreOf 2 (LOf L V₁) := by
  have h1 : ⁅ROf T L V₁, LOf L V₁⁆ ≤ ROf T L V₁ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (lOf_le_normalizer_rOf T L V₁)
  have h2 : ⁅ROf T L V₁, LOf L V₁⁆ ≤ LOf L V₁ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (rOf_le_normalizer_lOf h hV₁)
  refine (le_inf h1 h2).trans ?_
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
    (fun l hl => SecD.mem_normalizer_inf (lOf_le_normalizer_rOf T L V₁ hl)
      (Subgroup.le_normalizer hl))
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)

theorem exists_lOf_iso (h1110 : Stmt11_1_0) (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hn : n = 2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥(LOf L V₁) ⧸ CFSG.pCore 2 ↥(LOf L V₁) ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨F, i1, i2, hF, he⟩ := (h1110 G T L I n h).2.1 1 (Or.inl rfl) V₁ hV₁
  subst hn
  exact ⟨F, i1, i2, by simpa using hF, he⟩

theorem commutator_rOf_le_oTwoTwoPrime (hSig : SL2pSignalizerFact) (h1110 : Stmt11_1_0)
    (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hn : n = 2)
    {K : Subgroup G} (hLK : LOf L V₁ ≤ K) (hTK : T ≤ Subgroup.normalizer (K : Set G)) {p : ℕ}
    [Fact p.Prime] (h11 : 11 ≤ p) (φ : ↥K →* SL(2, ZMod p)) (hφs : Function.Surjective φ)
    (hφk : ∀ k : ↥K, φ k = 1 ↔ (k : G) ∈ oTwoTwoPrime K) :
    ⁅ROf T L V₁, K⁆ ≤ oTwoTwoPrime K := by
  obtain ⟨F, _, _, hF, he⟩ := exists_lOf_iso h1110 h hV₁ hn
  refine hSig G K (LOf L V₁) (ROf T L V₁) p Fact.out (Or.inr h11) ⟨φ, hφs, ?_⟩ hLK
    (perfectCore_perfect _) ⟨F, inferInstance, inferInstance, hF, he⟩ ((rOf_le_T h V₁).trans hTK)
    (rOf_le_normalizer_lOf h hV₁) (commutator_rOf_lOf_le h hV₁)
  ext k
  rw [MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf]

theorem pCoreOf_le_rOf' (h : Hyp11 G T L I n) {V₁ K : Subgroup G} (hLK : LOf L V₁ ≤ K)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) : pCoreOf 2 K ≤ ROf T L V₁ := by
  refine le_trans ?_ (pCoreOf_le_rOf h hLK)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
    ((sup_le Subgroup.le_normalizer hTK).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)

theorem rOf_le_normalizer_oTwoTwoPrime (h : Hyp11 G T L I n) {V₁ K : Subgroup G}
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    ROf T L V₁ ≤ Subgroup.normalizer (oTwoTwoPrime K : Set G) :=
  (rOf_le_T h V₁).trans (hTK.trans (SecD.normalizer_le_normalizer_oTwoTwoPrime K))

theorem isSylowTwoOf_rOf_sup (h : Hyp11 G T L I n) {V₁ K : Subgroup G} (hLK : LOf L V₁ ≤ K)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    QuasithinUnique.IsSylowTwoOf (ROf T L V₁) (ROf T L V₁ ⊔ oTwoTwoPrime K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := ROf T L V₁ with hR
  set O := oTwoTwoPrime K with hO
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRO : R ≤ Subgroup.normalizer (O : Set G) := rOf_le_normalizer_oTwoTwoPrime h hTK
  have hOR := pCoreOf_le_rOf' h hLK hTK
  refine ⟨le_sup_left, hR2, ?_⟩
  have hRW : IsPGroup 2 (R.subgroupOf (R ⊔ O)) :=
    hR2.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_left).symm
  obtain ⟨P, hP⟩ := hRW.exists_le_sylow
  have hPR : (P : Subgroup ↥(R ⊔ O)) ≤ R.subgroupOf (R ⊔ O) := by
    intro s hs
    have hsW : (s : G) ∈ ((R ⊔ O : Subgroup G) : Set G) := s.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right R O hRO] at hsW
    obtain ⟨r, hr, o, ho, hro⟩ := hsW
    have hrP : (⟨r, Subgroup.mem_sup_left hr⟩ : ↥(R ⊔ O)) ∈ P :=
      hP (Subgroup.mem_subgroupOf.mpr hr)
    have hoP : (⟨o, Subgroup.mem_sup_right ho⟩ : ↥(R ⊔ O)) ∈ P := by
      have e : (⟨o, Subgroup.mem_sup_right ho⟩ : ↥(R ⊔ O)) =
          (⟨r, Subgroup.mem_sup_left hr⟩ : ↥(R ⊔ O))⁻¹ * s :=
        Subtype.ext (by simp [← hro])
      rw [e]
      exact P.mul_mem (P.inv_mem hrP) hs
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨_, hoP⟩
    have ho2 : o ^ 2 ^ k = 1 := by
      have := congrArg (fun x : ↥(P : Subgroup ↥(R ⊔ O)) => ((x : ↥(R ⊔ O)) : G)) hk
      simpa using this
    have hoR : o ∈ R := hOR (SecD.mem_pCoreOf_of_mem_oTwoTwoPrime ho ho2)
    rw [Subgroup.mem_subgroupOf, ← hro]
    exact R.mul_mem hr hoR
  have heq : (P : Subgroup ↥(R ⊔ O)) = R.subgroupOf (R ⊔ O) := le_antisymm hPR hP
  rw [← heq]
  exact P.not_dvd_index

theorem exists_mul_of_rOf (h : Hyp11 G T L I n) {V₁ K : Subgroup G} (hLK : LOf L V₁ ≤ K)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hRK : ⁅ROf T L V₁, K⁆ ≤ oTwoTwoPrime K) :
    ∀ g ∈ K, ∃ o ∈ oTwoTwoPrime K, ∃ k ∈ K ⊓ Subgroup.normalizer (ROf T L V₁ : Set G),
      g = o * k := by
  set R := ROf T L V₁ with hR
  set O := oTwoTwoPrime K with hO
  have hRO : R ≤ Subgroup.normalizer (O : Set G) := rOf_le_normalizer_oTwoTwoPrime h hTK
  have hOK : O ≤ K := SecD.oTwoTwoPrime_le K
  have hKO : K ≤ Subgroup.normalizer (O : Set G) :=
    Subgroup.le_normalizer.trans (SecD.normalizer_le_normalizer_oTwoTwoPrime K)
  have hWN : R ⊔ O ≤ K ⊔ R := sup_le le_sup_right (hOK.trans le_sup_left)
  have hNW : K ⊔ R ≤ Subgroup.normalizer ((R ⊔ O : Subgroup G) : Set G) := by
    refine sup_le (fun k hk => ?_) (fun r hr => ?_)
    · refine mem_normalizer_sup_of_comm (hKO hk) fun r hr => ?_
      have := hRK (Subgroup.commutator_mem_commutator hr hk)
      rwa [commutatorElement_def] at this
    · exact mem_normalizer_sup_of (Subgroup.le_normalizer hr) (hRO hr)
  intro g hg
  obtain ⟨x, hx, m, hm, rfl⟩ := exists_mul_of_frattini hWN hNW (isSylowTwoOf_rOf_sup h hLK hTK) g
    (Subgroup.mem_sup_left hg)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right R O hRO] at hx
  obtain ⟨r, hr, o, ho, rfl⟩ := hx
  have hro : r * o * r⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hRO hr) o).mp ho
  refine ⟨r * o * r⁻¹, hro, r * m, ⟨?_, Subgroup.mul_mem _ (Subgroup.le_normalizer hr) hm.2⟩,
    by group⟩
  have e : r * m = (r * o * r⁻¹)⁻¹ * (r * o * m) := by group
  rw [e]
  exact K.mul_mem (K.inv_mem (hOK hro)) hg

end CFSG.Quasithin.Vol2.Ch11.SecE
