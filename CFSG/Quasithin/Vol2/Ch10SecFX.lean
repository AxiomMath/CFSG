module

public import CFSG.Quasithin.Vol2.Ch10SecEE3Alt
public import CFSG.Quasithin.Vol2.Ch10SecA1012Four
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5VecAux
public import CFSG.Quasithin.Vol2.Ch10SecB6C23
public import CFSG.Quasithin.Vol2.Ch10SecEBlock
public import CFSG.Quasithin.Vol2.Ch10SecEOver

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem fsuCVM_eq_bot_case2 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I) : fsuCVM T L I = ⊥ := by
  refine SecA.fsuCVM_eq_bot_of_cV1 h37 h38 hyp (le_bot_iff.mp fun u hu => ?_)
  obtain ⟨-, hcU, hA⟩ := h2
  have hLV : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    SecA.le_normalizer_commutator ((SecA.le_fsuL0 T L).trans
      (SecA.fsuL0_le_normalizer_fsuVM T L I)) Subgroup.le_normalizer
  have huL : (u : G) ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.centralizer_le (SecA.le_fsuL0 T L) (Subgroup.mem_subgroupOf.mp hu)
  have h1 : u = 1 := by
    refine SecE.eq_one_of_alternatingNatural_five hA fun φ hφ => ?_
    obtain ⟨⟨g, hgN⟩, hgL, rfl⟩ := Subgroup.mem_map.mp hφ
    apply Subtype.ext
    show g * (u : G) * g⁻¹ = u
    rw [Subgroup.mem_centralizer_iff.mp huL g (Subgroup.mem_subgroupOf.mp hgL)]
    simp
  rw [h1]
  exact Subgroup.one_mem _

theorem fsuUL_inf_conjugate_eq_bot (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I)
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    fsuUL T L I ⊓ CFSG.conjugate (fsuUL T L I) t = ⊥ :=
  le_bot_iff.mp ((SecA.inf_conjugate_le_fsuCVM hyp ht htn).trans
    (fsuCVM_eq_bot_case2 h37 h38 hyp h2).le)

theorem conjugate_fsuUL_eq_or (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {s : G} (hs : s ∈ fsuM T L) :
    CFSG.conjugate (fsuUL T L I) s = fsuUL T L I ∨
      CFSG.conjugate (fsuUL T L I) s = CFSG.conjugate (fsuUL T L I) t := by
  rw [SecA.conjugate_commutator_fsuVM hs, SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht)]
  rcases SecA.conjugate_eq_or h37 h38 hyp ht htn hs with h | h
  · left
    rw [h]
  · right
    rw [h]

omit [Finite G] in
theorem mem_conjugate_iff' {X : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate X g ↔ g * x * g⁻¹ ∈ X :=
  SecA.mem_conjugate_iff

theorem eq_one_of_le_centralizer (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I)
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {u : G}
    (hu : u ∈ fsuUL T L I ∨ u ∈ CFSG.conjugate (fsuUL T L I) t)
    (hT : T ≤ Subgroup.centralizer ({u} : Set G)) : u = 1 := by
  have htu : t * u * t⁻¹ = u := by
    have := Subgroup.mem_centralizer_iff.mp (hT ht) u rfl
    rw [← this]
    group
  have hmem : u ∈ fsuUL T L I ⊓ CFSG.conjugate (fsuUL T L I) t := by
    rcases hu with hu | hu
    · refine ⟨hu, mem_conjugate_iff'.mpr ?_⟩
      rw [htu]
      exact hu
    · refine ⟨?_, hu⟩
      have := mem_conjugate_iff'.mp hu
      rwa [htu] at this
  rw [fsuUL_inf_conjugate_eq_bot h37 h38 hyp h2 ht htn] at hmem
  exact hmem

omit [Finite G] in
theorem exists_mem_normalizer_not_mem_of_lt {p : ℕ} [Fact p.Prime] {P Q : Subgroup G}
    [Finite Q] (hQ : IsPGroup p Q) (hPQ : P < Q) :
    ∃ x ∈ Q, x ∉ P ∧ x ∈ Subgroup.normalizer (P : Set G) := by
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hlt : P.subgroupOf Q < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hPQ.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : Q) ∈ P.subgroupOf Q := by
      rw [htop]
      trivial
    exact Subgroup.mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := Q) _ hlt)
  refine ⟨y, y.2, fun h => hyP (Subgroup.mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (Subgroup.normalizer (P : Set G)).subgroupOf Q := by
    rw [Subgroup.subgroupOf_normalizer_eq hPQ.le]
    exact hyN
  exact Subgroup.mem_subgroupOf.mp hy

theorem exists_conj_of_not_isSylowTwoOf (hT : quasithinIsSylowTwo T) {T₁ X : Subgroup G}
    (hT₁T : T₁ ≤ T) (hidx : (T₁.subgroupOf T).index = 2)
    (hTN : T ≤ Subgroup.normalizer (T₁ : Set G)) (hT₁X : T₁ ≤ X) (hns : ¬ IsSylowTwoOf T₁ X) :
    ∃ m ∈ Subgroup.normalizer (T₁ : Set G), T ≤ B6.conjSub m X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT₁2 : IsPGroup 2 T₁ := hT.1.to_le hT₁T
  obtain ⟨S, hS, hT₁S⟩ := B6.exists_isSylowTwoOf_ge hT₁2 hT₁X
  have hlt : T₁ < S := lt_of_le_of_ne hT₁S fun h => hns (h ▸ hS)
  obtain ⟨y, hyS, hyT₁, hyN⟩ := exists_mem_normalizer_not_mem_of_lt hS.2.1 hlt
  set N := Subgroup.normalizer (T₁ : Set G) with hNdef
  have hy2 : IsPGroup 2 (Subgroup.zpowers y) :=
    hS.2.1.to_le (Subgroup.zpowers_le.mpr hyS)
  have hQ2 : IsPGroup 2 (T₁ ⊔ Subgroup.zpowers y : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hT₁2 hy2 (Subgroup.zpowers_le.mpr hyN)
  have hQN : T₁ ⊔ Subgroup.zpowers y ≤ N :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hyN)
  obtain ⟨S', hS', hQS'⟩ := B6.exists_isSylowTwoOf_ge hQ2 hQN
  obtain ⟨g, hgN, hgS'⟩ :=
    B6.isSylowTwoOf_exists_conj (isSylowTwoOf_of_quasithinIsSylowTwo hT hTN) hS'
  have hyS' : y ∈ B6.conjSub g T :=
    hgS' ▸ hQS' ((le_sup_right : Subgroup.zpowers y ≤ T₁ ⊔ Subgroup.zpowers y)
      (Subgroup.mem_zpowers y))
  set r := g⁻¹ * y * g with hr
  have hrT : r ∈ T := B6.mem_conjSub.mp hyS'
  have hrT₁ : r ∉ T₁ := by
    intro h
    apply hyT₁
    have := (Subgroup.mem_normalizer_iff.mp hgN r).mp h
    simpa [hr, mul_assoc] using this
  refine ⟨g⁻¹, N.inv_mem hgN, fun x hx => ?_⟩
  rw [B6.mem_conjSub, inv_inv]
  by_cases hxT₁ : x ∈ T₁
  · exact hT₁X ((Subgroup.mem_normalizer_iff.mp hgN x).mp hxT₁)
  · have hmul : (⟨x, hx⟩ : ↥T) * (⟨r, hrT⟩ : ↥T)⁻¹ ∈ T₁.subgroupOf T := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      simp only [Subgroup.mem_subgroupOf, inv_mem_iff]
      exact iff_of_false hxT₁ hrT₁
    have ha : x * r⁻¹ ∈ T₁ := Subgroup.mem_subgroupOf.mp hmul
    have hga := hT₁X ((Subgroup.mem_normalizer_iff.mp hgN _).mp ha)
    have e : g * x * g⁻¹ = g * (x * r⁻¹) * g⁻¹ * y := by
      simp only [hr]
      group
    rw [e]
    exact X.mul_mem hga (hS.1 hyS)

omit [Finite G] in
theorem mem_centralizer_conj {m w x : G}
    (h : m⁻¹ * x * m ∈ Subgroup.centralizer ({w} : Set G)) :
    x ∈ Subgroup.centralizer ({m * w * m⁻¹} : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at h ⊢
  rintro _ rfl
  have h1 := h w rfl
  calc m * w * m⁻¹ * x = m * (w * (m⁻¹ * x * m)) * m⁻¹ := by group
    _ = m * ((m⁻¹ * x * m) * w) * m⁻¹ := by rw [h1]
    _ = x * (m * w * m⁻¹) := by group

theorem isSylowTwoOf_T1_centralizer
    (h311 : Theorem311Stmt) (h331 : Stmt3_3_1)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hshape : Stmt7_0_1_shape) (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I)
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {w : G}
    (hw : w ∈ CFSG.conjugate (fsuUL T L I) t) (hw1 : w ≠ 1)
    (hT1 : Ch10.T1 T L ≤ Subgroup.centralizer ({w} : Set G)) :
    IsSylowTwoOf (Ch10.T1 T L) (Subgroup.centralizer ({w} : Set G)) := by
  by_contra hns
  obtain ⟨m, hmN, hTm⟩ := exists_conj_of_not_isSylowTwoOf hyp.fsu.sylow inf_le_left
    (SecA.index_T1 h37 h38 hyp) (SecE.le_normalizer_T1 h37 h38 hyp) hT1 hns
  have hmM : m ∈ fsuM T L :=
    SecE.normalizer_T1_le h311 h331 h37 h38 hshape hyp (Or.inr h2) hmN
  have hTc : T ≤ Subgroup.centralizer ({m * w * m⁻¹} : Set G) :=
    fun x hx => mem_centralizer_conj (B6.mem_conjSub.mp (hTm hx))
  have hsM : t * m⁻¹ ∈ fsuM T L := (fsuM T L).mul_mem (SecA.le_fsuM T L ht)
    ((fsuM T L).inv_mem hmM)
  have hmem : m * w * m⁻¹ ∈ CFSG.conjugate (fsuUL T L I) (t * m⁻¹) := by
    rw [mem_conjugate_iff']
    have := mem_conjugate_iff'.mp hw
    simpa [mul_assoc] using this
  have hmem' : m * w * m⁻¹ ∈ fsuUL T L I ∨
      m * w * m⁻¹ ∈ CFSG.conjugate (fsuUL T L I) t := by
    rcases conjugate_fsuUL_eq_or h37 h38 hyp ht htn hsM with h | h
    · exact Or.inl (h ▸ hmem)
    · exact Or.inr (h ▸ hmem)
  have h1 := eq_one_of_le_centralizer h37 h38 hyp h2 ht htn hmem' hTc
  apply hw1
  calc w = m⁻¹ * (m * w * m⁻¹) * m := by group
    _ = 1 := by rw [h1]; group

theorem exists_cComp_centralizer (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (hyp : Hyp10 G T L I)
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {w : G}
    (hw : w ∈ CFSG.conjugate (fsuUL T L I) t) (hw1 : w ≠ 1)
    (hsyl : IsSylowTwoOf (Ch10.T1 T L) (Subgroup.centralizer ({w} : Set G))) :
    CFSG.SectionRank.IsSQTKCat ↥(Subgroup.centralizer ({w} : Set G)) ∧
      L ≤ Subgroup.centralizer ({w} : Set G) ∧
      ∃ J ∈ cComp (Subgroup.centralizer ({w} : Set G)), L ≤ J ∧
        Ch10.T1 T L ≤ Subgroup.normalizer (J : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := hyp.fsu.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  set X := Subgroup.centralizer ({w} : Set G) with hXdef
  have hwV : w ∈ fsuVM T L I := SecA.conjugate_fsuUL_le (SecA.le_fsuM T L ht) hw
  have hw2 : IsPGroup 2 (Subgroup.zpowers w) :=
    (SecA.isPGroup_fsuVM hyp).to_le (Subgroup.zpowers_le.mpr hwV)
  have hX2 : pCoreOf 2 X ≠ ⊥ := by
    intro hb
    apply hw1
    have := SecB.mem_pCoreOf_centralizer hw2
    rw [← hXdef, hb] at this
    exact this
  have hLX : L ≤ X := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact (Subgroup.mem_centralizer_iff.mp
      (SecA.conjugate_fsuUL_le_centralizer h37 h38 hyp ht htn hw) l hl).symm
  have hLfam : L ∈ lFamily (Ch10.T1 T L) :=
    cComp_mem_of_le (SecE.mem_cComp_L0T hyp) le_sup_left
      (sup_le ((SecA.le_fsuL0 T L).trans le_sup_left) (inf_le_left.trans le_sup_right))
  obtain ⟨J, hJ, hLJ⟩ := Vol2Native.lemma_1_2_4_exists hK h37 h39 hX2 hsyl hLX hLfam
  refine ⟨hK X hX2, hLX, J, hJ, hLJ, fun x hx => ?_⟩
  have hxX : x ∈ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer (hsyl.1 hx)
  have hJx := SecB.map_conj_mem_cComp' hJ hxX
  have hLJx : L ≤ J.map (MulAut.conj x).toMonoidHom := by
    have h := Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) hLJ
    rwa [A38.map_conj_eq_iff.mpr hx.2] at h
  have heq := Vol2Native.lemma_1_2_4_unique hK h37 hX2 hLfam hJ hJx hLJ hLJx
  exact A38.map_conj_eq_iff.mp heq.symm

end CFSG.Quasithin.Vol2.Ch10.SecF
