module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.theorem_1_13
public import CFSG.RankThree.PartTwo.Sec13.Item135CritProof
public import CFSG.LocalAnalysis.LargeEvenClassification.FrattiniKernel
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_exp3_normal_coprime (hQ : CFSG.pCore 3 G ≠ ⊥) :
    ∃ D : Subgroup G, D ≤ CFSG.pCore 3 G ∧ D.Normal ∧ (∀ x ∈ D, x ^ 3 = 1) ∧
      ∀ c : G, Nat.Coprime (orderOf c) 3 → c ∈ Subgroup.centralizer (D : Set G) →
        c ∈ Subgroup.centralizer (CFSG.pCore 3 G : Set G) := by
  let Q : Subgroup G := CFSG.pCore 3 G
  haveI : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ
  haveI : Fact (IsPGroup 3 Q) := ⟨CFSG.pCore_isPGroup (p := 3) (G := G)⟩
  haveI : Q.Characteristic := CFSG.pCore_characteristic (p := 3) (G := G)
  have hpodd : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨H, hHchar, -, -, hHexp, hHfix⟩ :=
    CFSG.theorem_1_13 (G := Q) (p := 3) hpodd
  haveI : H.Characteristic := hHchar
  have hDchar : (H.map Q.subtype).Characteristic := inferInstance
  refine ⟨H.map Q.subtype, Subgroup.map_subtype_le H, inferInstance, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hy3 : (⟨y, hy⟩ : H) ^ 3 = 1 := by
      have h := Monoid.pow_exponent_eq_one (⟨y, hy⟩ : H)
      rwa [hHexp] at h
    have hy3' : (y : Q) ^ 3 = 1 := by simpa using congrArg Subtype.val hy3
    simpa using congrArg (fun z : Q => (z : G)) hy3'
  · intro c hccop hc
    have hc' : ∀ x ∈ Q, c * x * c⁻¹ = x :=
      CFSG.RankThree.PartTwo.Sec13.CritProof.centralizes_of_coprime_of_fixing
        (Q := Q) (D₀ := (H : Set Q)) hHfix
        (by rw [Subgroup.normalizer_eq_top]; trivial) hccop (fun d hd => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (mul_inv_eq_iff_eq_mul.mp (hc' x hx)).symm
    · have hmem : (d : G) ∈ H.map Q.subtype := Subgroup.mem_map_of_mem Q.subtype hd
      have hcomm := (Subgroup.mem_centralizer_iff.mp hc) (d : G) hmem
      rw [← hcomm]; group

theorem centralizer_le_pCore_of_coprime {D : Subgroup G} (hD : D.Normal)
    (hcop : ∀ c : G, Nat.Coprime (orderOf c) 3 → c ∈ Subgroup.centralizer (D : Set G) →
      c ∈ Subgroup.centralizer (CFSG.pCore 3 G : Set G))
    (hcent : Subgroup.centralizer (CFSG.pCore 3 G : Set G) ≤ CFSG.pCore 3 G) :
    Subgroup.centralizer (D : Set G) ≤ CFSG.pCore 3 G := by
  let C : Subgroup G := Subgroup.centralizer (D : Set G)
  haveI : D.Normal := hD
  haveI : C.Normal := Subgroup.normal_centralizer
  have hCp : IsPGroup 3 C := by
    intro g
    have hn0 : orderOf (g : G) ≠ 0 := (orderOf_pos (g : G)).ne'
    let k : ℕ := ordProj[3] (orderOf (g : G))
    have hk_dvd : k ∣ orderOf (g : G) := Nat.ordProj_dvd (orderOf (g : G)) 3
    have hk_ne : k ≠ 0 := (Nat.ordProj_pos (orderOf (g : G)) 3).ne'
    have hc_cop : Nat.Coprime (orderOf ((g : G) ^ k)) 3 := by
      rw [orderOf_pow_of_dvd hk_ne hk_dvd]
      exact (Nat.coprime_ordCompl (p := 3) (by norm_num) hn0).symm
    have hc_mem : (g : G) ^ k ∈ C := (g ^ k).2
    have hQmem : (g : G) ^ k ∈ CFSG.pCore 3 G := hcent (hcop ((g : G) ^ k) hc_cop hc_mem)
    obtain ⟨m, hm⟩ := CFSG.pCore_isPGroup (p := 3) (G := G) ⟨(g : G) ^ k, hQmem⟩
    have hm' : ((g : G) ^ k) ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hord1 : orderOf ((g : G) ^ k) = 1 := by
      have hdvd : orderOf ((g : G) ^ k) ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hm'
      have hc3 : Nat.Coprime (orderOf ((g : G) ^ k)) (3 ^ m) := hc_cop.pow_right m
      have hdvd1 : orderOf ((g : G) ^ k) ∣ 1 := by
        rw [← hc3.gcd_eq_one]
        exact Nat.dvd_gcd (dvd_refl _) hdvd
      exact Nat.dvd_one.mp hdvd1
    have hk1 : (g : G) ^ k = 1 := orderOf_eq_one_iff.mp hord1
    refine ⟨(orderOf (g : G)).factorization 3, Subtype.ext ?_⟩
    simpa [k] using hk1
  exact le_sSup ⟨inferInstance, hCp⟩

private lemma mem_frattiniKernel_conjNormal_iff {Q : Subgroup G} [Q.Normal] {h : G} :
    MulAut.conjNormal h ∈ CFSG.LargeEvenClassification.Helpers.frattiniKernel Q ↔
      ∀ x ∈ Q, h * x * h⁻¹ * x⁻¹ ∈ (frattini Q).map Q.subtype := by
  constructor
  · intro hk x hx
    have hk' : ∀ element : Q, ((MulAut.conjNormal h) element : Q ⧸ frattini Q) =
        (element : Q ⧸ frattini Q) := hk
    have h1 := hk' ⟨x, hx⟩
    rw [QuotientGroup.eq_iff_div_mem] at h1
    refine Subgroup.mem_map.mpr ⟨MulAut.conjNormal h ⟨x, hx⟩ / ⟨x, hx⟩, h1, ?_⟩
    simp [MulAut.conjNormal_apply, Subgroup.coe_div, Subgroup.coe_inv, div_eq_mul_inv]
  · intro hfix
    change ∀ element : Q, ((MulAut.conjNormal h) element : Q ⧸ frattini Q) =
      (element : Q ⧸ frattini Q)
    intro x
    rw [QuotientGroup.eq_iff_div_mem]
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp (hfix (x : G) x.2)
    have hy' : y = MulAut.conjNormal h x / x := by
      apply Subtype.ext
      have hyeq' : (y : G) = h * x * h⁻¹ * x⁻¹ := hyeq
      rw [hyeq']
      simp [MulAut.conjNormal_apply, Subgroup.coe_div, Subgroup.coe_inv, div_eq_mul_inv]
    rwa [hy'] at hy

theorem mem_pCore_of_trivial_on_frattini {p : ℕ} [Fact p.Prime]
    (hcent : Subgroup.centralizer (CFSG.pCore p G : Set G) ≤ CFSG.pCore p G) {g : G}
    (hg : ∀ x ∈ CFSG.pCore p G,
      g * x * g⁻¹ * x⁻¹ ∈ (frattini ↥(CFSG.pCore p G)).map (CFSG.pCore p G).subtype) :
    g ∈ CFSG.pCore p G := by
  let Q : Subgroup G := CFSG.pCore p G
  haveI : Q.Normal := CFSG.pCore_normal (p := p) (G := G)
  let K : Subgroup G :=
    (CFSG.LargeEvenClassification.Helpers.frattiniAutAction Q).ker.comap (MulAut.conjNormal)
  have hKnormal : K.Normal := by dsimp [K]; infer_instance
  have hKp : IsPGroup p K := by
    intro h
    have hmem : MulAut.conjNormal (h : G) ∈
        (CFSG.LargeEvenClassification.Helpers.frattiniAutAction Q).ker :=
      Subgroup.mem_comap.mp h.2
    obtain ⟨k, hk⟩ := CFSG.LargeEvenClassification.Helpers.frattiniAutAction_isPGroup_ker Q
      (Fact.out) (CFSG.pCore_isPGroup (p := p) (G := G)) ⟨MulAut.conjNormal (h : G), hmem⟩
    have hk' : (MulAut.conjNormal (H := Q) (h : G)) ^ p ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have hconj1 : MulAut.conjNormal (H := Q) ((h : G) ^ p ^ k) = 1 := by
      rw [map_pow, hk']
    have hcentQ : (h : G) ^ p ^ k ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have happ : MulAut.conjNormal (H := Q) ((h : G) ^ p ^ k) ⟨x, hx⟩ = ⟨x, hx⟩ := by
        have h1 := congrArg (fun φ : MulAut Q => φ ⟨x, hx⟩) hconj1
        simpa only [MulAut.one_apply] using h1
      have h2 := congrArg (fun y : Q => (y : G)) happ
      rw [MulAut.conjNormal_apply] at h2
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    have hQmem : (h : G) ^ p ^ k ∈ Q := hcent hcentQ
    obtain ⟨m, hm⟩ := CFSG.pCore_isPGroup (p := p) (G := G) ⟨(h : G) ^ p ^ k, hQmem⟩
    have hm' : ((h : G) ^ p ^ k) ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
    refine ⟨k + m, Subtype.ext ?_⟩
    have hm'' : (h : G) ^ (p ^ (k + m)) = 1 := by
      simpa [pow_add, pow_mul] using hm'
    simpa using hm''
  have hgK : g ∈ K := by
    change MulAut.conjNormal (H := Q) g ∈
      (CFSG.LargeEvenClassification.Helpers.frattiniAutAction Q).ker
    rw [CFSG.LargeEvenClassification.Helpers.frattiniAutAction_ker]
    exact mem_frattiniKernel_conjNormal_iff.mpr (fun x hx => hg x hx)
  change g ∈ sSup {K' : Subgroup G | K'.Normal ∧ IsPGroup p K'}
  exact (le_sSup (s := {K' : Subgroup G | K'.Normal ∧ IsPGroup p K'})
    ⟨hKnormal, hKp⟩) hgK

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
