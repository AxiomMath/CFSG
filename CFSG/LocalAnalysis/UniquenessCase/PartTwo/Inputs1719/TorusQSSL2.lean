module

public import CFSG.RankThree.GF2n.Smith81.Lin22SL2
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93AC2
public import CFSG.RankThree.PartOne.KFCL.L4Block
public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.TorusProd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS

open scoped MatrixGroups commutatorElement
open CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Smith81

private theorem eq_bot_of_perfect_of_commutator_le {G : Type*} [Group G] {Q H A : Subgroup G}
    (hQ : ⁅Q, Q⁆ = Q) (hQH : Q ≤ H) (hHA : ⁅H, H⁆ ≤ A)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : Q = ⊥ := by
  have hQA : Q ≤ A := by
    calc Q = ⁅Q, Q⁆ := hQ.symm
      _ ≤ ⁅H, H⁆ := Subgroup.commutator_mono hQH hQH
      _ ≤ A := hHA
  have h : ⁅Q, Q⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hA y (hQA hy) x (hQA hx)
  rw [← hQ, h]

section SL2F

variable {F : Type} [Field F]

private theorem commutator_borel_le_utri : ⁅borel F, borel F⁆ ≤ utri F := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  have hg' : g 1 0 = 0 := hg
  have hh' : h 1 0 = 0 := hh
  have hmem : ⁅g, h⁆ ∈ borel F := by
    rw [commutatorElement_def]
    exact (borel F).mul_mem ((borel F).mul_mem ((borel F).mul_mem hg hh) ((borel F).inv_mem hg))
      ((borel F).inv_mem hh)
  refine mem_utri_entries.2 ⟨hmem, ?_⟩
  have hdg := sl2_det g
  have hdh := sl2_det h
  rw [hg'] at hdg
  rw [hh'] at hdh
  rw [commutatorElement_def, mul_apply_00, mul_apply_00, mul_apply_00, inv_apply_10,
    inv_apply_10, hg', hh', inv_apply_00, inv_apply_00]
  linear_combination (h 0 0 * h 1 1) * hdg + hdh

private theorem utri_comm {a b : SL(2, F)} (ha : a ∈ utri F) (hb : b ∈ utri F) :
    a * b = b * a := by
  obtain ⟨s, rfl⟩ := mem_utri_iff.1 ha
  obtain ⟨t, rfl⟩ := mem_utri_iff.1 hb
  rw [← utriElt_add, ← utriElt_add, add_comm]

private theorem torus_comm {a b : SL(2, F)} (ha : a ∈ torus F) (hb : b ∈ torus F) :
    a * b = b * a := by
  obtain ⟨s, rfl⟩ := mem_torus_iff.1 ha
  obtain ⟨t, rfl⟩ := mem_torus_iff.1 hb
  rw [← torusElt_mul, ← torusElt_mul, mul_comm]

private theorem conj_utri_comm (c : SL(2, F)) {a b : SL(2, F)} (ha : a ∈ conjSubgroup c (utri F))
    (hb : b ∈ conjSubgroup c (utri F)) : a * b = b * a := by
  rw [mem_conjSubgroup] at ha hb
  have h := utri_comm ha hb
  calc a * b = c * ((c⁻¹ * a * c) * (c⁻¹ * b * c)) * c⁻¹ := by group
    _ = c * ((c⁻¹ * b * c) * (c⁻¹ * a * c)) * c⁻¹ := by rw [h]
    _ = b * a := by group

variable [Finite F] [CharP F 2]

private theorem commutator_normalizer_torus_le (h4 : 4 ≤ Nat.card F) :
    ⁅Subgroup.normalizer (torus F : Set SL(2, F)), Subgroup.normalizer (torus F : Set SL(2, F))⁆ ≤
      torus F := by
  set N := Subgroup.normalizer (torus F : Set SL(2, F)) with hNdef
  have hTN : torus F ≤ N := Subgroup.le_normalizer
  have hidx : ((torus F).subgroupOf N).index = 2 := by
    have hN := SL2Torus.card_normalizer_torus h4
    have hT := card_torus (F := F)
    have hmul := Subgroup.card_mul_index ((torus F).subgroupOf N)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv, hT] at hmul
    have hpos : 0 < Nat.card F - 1 := by omega
    rw [← hNdef] at hN
    rw [hN] at hmul
    have : (Nat.card F - 1) * ((torus F).subgroupOf N).index = (Nat.card F - 1) * 2 := by
      rw [hmul]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have key : (⁅(⟨a, ha⟩ : N), ⟨b, hb⟩⁆ : N) ∈ (torus F).subgroupOf N := by
    rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hidx,
      Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
      Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
    tauto
  simpa [Subgroup.mem_subgroupOf, commutatorElement_def] using key

theorem perfect_eq_bot_or_top_of_torus (h4 : 4 ≤ Nat.card F) {Q : Subgroup SL(2, F)}
    (hQ : ⁅Q, Q⁆ = Q) (hTQ : torus F ≤ Subgroup.normalizer (Q : Set SL(2, F))) :
    Q = ⊥ ∨ Q = ⊤ := by
  set N := Q ⊔ torus F with hNdef
  have hNQ : N ≤ Subgroup.normalizer (Q : Set SL(2, F)) := sup_le Subgroup.le_normalizer hTQ
  by_cases hO : ∀ P : Subgroup SL(2, F), P ≤ N →
      N ≤ Subgroup.normalizer (P : Set SL(2, F)) → IsPGroup 2 P → P = ⊥
  · rcases SL2Torus.le_normalizer_torus_or_eq_top h4 le_sup_right hO with hle | htop
    · exact Or.inl (eq_bot_of_perfect_of_commutator_le hQ (le_sup_left.trans hle)
        (commutator_normalizer_torus_le h4) fun a ha b hb => torus_comm ha hb)
    · have hQn : Q.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (htop ▸ hNQ))
      have := CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup h4
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal Q
  · push Not at hO
    obtain ⟨P, -, hNP, hP2, hPne⟩ := hO
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨S, hPS⟩ := hP2.exists_le_sylow
    obtain ⟨c, hc⟩ := exists_conjSubgroup_utri_eq_of_sylow S
    have hPc : P ≤ conjSubgroup c (utri F) := hc ▸ hPS
    have hNB : N ≤ conjSubgroup c (borel F) :=
      hNP.trans (CFSG.RankThree.GF2n.Stroth80.sl2_normalizer_le_conj_borel hPc hPne)
    refine Or.inl (eq_bot_of_perfect_of_commutator_le hQ (le_sup_left.trans hNB) ?_
      fun a ha b hb => conj_utri_comm c ha hb)
    change ⁅(borel F).map (MulAut.conj c).toMonoidHom, (borel F).map (MulAut.conj c).toMonoidHom⁆ ≤
      (utri F).map (MulAut.conj c).toMonoidHom
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono commutator_borel_le_utri

omit [Finite F] [CharP F 2] in
private theorem torusSL_eq_torus :
    CFSG.LocalAnalysis.EvenBN.Common.torusSL F = torus F := by
  ext g
  constructor
  · rintro ⟨μ, rfl⟩
    refine mem_torus_entries.2 ⟨?_, ?_⟩ <;>
      simp [CFSG.LocalAnalysis.EvenBN.Common.diagSLHom_apply,
        CFSG.LocalAnalysis.EvenBN.Common.coe_diagSL]
  · intro hg
    obtain ⟨h01, h10⟩ := mem_torus_entries.1 hg
    have hdet : g 0 0 * g 1 1 - 0 * 0 = 1 := by
      have := sl2_det g
      rw [h01, h10] at this
      linear_combination this
    have hgeq : g = CFSG.LocalAnalysis.EvenBN.Common.mkSL (g 0 0) 0 0 (g 1 1) hdet := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [CFSG.LocalAnalysis.EvenBN.Common.coe_mkSL, h01, h10]
    rw [hgeq]
    exact CFSG.LocalAnalysis.EvenBN.Common.mkSL_mem_torusSL _ _ hdet

end SL2F

section L2

open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem exists_sl2_of_isL2 {Y : Type} [Group Y] {n : ℕ} (h : IsL2 Y n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ n ∧
      Nonempty (Y ≃* SL(2, F)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  exact ⟨K, inferInstance, inferInstance, inferInstance, hK,
    ⟨e.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_two_equiv K)⟩⟩

theorem perfect_eq_bot_or_top_of_isL2 {Y : Type} [Group Y] {n : ℕ} (hn : 2 ≤ n)
    (hY : IsL2 Y n) {d : Y} (hd1 : d ≠ 1) (hd : d ^ (2 ^ n - 1) = 1) {Q : Subgroup Y}
    (hQ : ⁅Q, Q⁆ = Q)
    (hCQ : Subgroup.centralizer ({d} : Set Y) ≤ Subgroup.normalizer (Q : Set Y)) :
    Q = ⊥ ∨ Q = ⊤ := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := exists_sl2_of_isL2 hY
  have hd' : d ^ (Nat.card F - 1) = 1 := by rw [hF]; exact hd
  obtain ⟨ψ, -, -, -, hC⟩ :=
    CFSG.LocalAnalysis.EvenBN.Common.exists_mulEquiv_map_centralizer_zpowers e hd1 hd'
  rw [CFSG.LocalAnalysis.EvenBN.Common.centralizer_zpowers, torusSL_eq_torus] at hC
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hQ' : ⁅Q.map ψ.toMonoidHom, Q.map ψ.toMonoidHom⁆ = Q.map ψ.toMonoidHom := by
    rw [← Subgroup.map_commutator, hQ]
  have hT : torus F ≤ Subgroup.normalizer ((Q.map ψ.toMonoidHom : Subgroup SL(2, F)) :
      Set SL(2, F)) := by
    rw [← hC, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hCQ
  rcases perfect_eq_bot_or_top_of_torus h4 hQ' hT with h | h
  · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).1 h)
  · right
    have h' := congrArg (Subgroup.comap ψ.toMonoidHom) h
    rwa [Subgroup.comap_map_eq_self_of_injective ψ.injective, Subgroup.comap_top] at h'

end L2

section Prod

variable {P₁ P₂ : Type} [Group P₁] [Group P₂]

theorem eq_top_of_fst_snd_eq_top [IsSimpleGroup P₁] {R : Subgroup (P₁ × P₂)}
    (hfst : R.map (MonoidHom.fst P₁ P₂) = ⊤) (hsnd : R.map (MonoidHom.snd P₁ P₂) = ⊤)
    {h : P₁} (hhZ : h ∉ Subgroup.center P₁)
    (hN : ((h, 1) : P₁ × P₂) ∈ Subgroup.normalizer (R : Set (P₁ × P₂))) : R = ⊤ := by
  have hfst' : ∀ a : P₁, ∃ b : P₂, ((a, b) : P₁ × P₂) ∈ R := by
    intro a
    have ha : a ∈ R.map (MonoidHom.fst P₁ P₂) := hfst ▸ Subgroup.mem_top a
    obtain ⟨⟨a', b⟩, hab, rfl⟩ := Subgroup.mem_map.mp ha
    exact ⟨b, hab⟩
  have hsnd' : ∀ b : P₂, ∃ a : P₁, ((a, b) : P₁ × P₂) ∈ R := by
    intro b
    have hb : b ∈ R.map (MonoidHom.snd P₁ P₂) := hsnd ▸ Subgroup.mem_top b
    obtain ⟨⟨a, b'⟩, hab, rfl⟩ := Subgroup.mem_map.mp hb
    exact ⟨a, hab⟩
  set K₁ : Subgroup P₁ := R.comap (MonoidHom.inl P₁ P₂) with hK₁def
  have hmemK : ∀ a : P₁, a ∈ K₁ ↔ ((a, 1) : P₁ × P₂) ∈ R := fun a => Iff.rfl
  have hK₁ : K₁.Normal := by
    refine ⟨fun a ha g => ?_⟩
    obtain ⟨b, hgb⟩ := hfst' g
    rw [hmemK] at ha ⊢
    have := R.mul_mem (R.mul_mem hgb ha) (R.inv_mem hgb)
    simpa using this
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K₁ with h1 | h1
  · exfalso
    refine hhZ (Subgroup.mem_center_iff.mpr fun a => ?_)
    obtain ⟨b, hab⟩ := hfst' a
    have hc : ((h, 1) : P₁ × P₂) * (a, b) * ((h, 1) : P₁ × P₂)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hN _).mp hab
    have hd := R.mul_mem hc (R.inv_mem hab)
    have hK : h * a * h⁻¹ * a⁻¹ ∈ K₁ := by
      rw [hmemK]
      simpa [mul_assoc] using hd
    rw [h1, Subgroup.mem_bot] at hK
    have : h * a * h⁻¹ = a := by
      calc h * a * h⁻¹ = h * a * h⁻¹ * a⁻¹ * a := by group
        _ = a := by rw [hK, one_mul]
    calc a * h = h * a * h⁻¹ * h := by rw [this]
      _ = h * a := by group
  · rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    obtain ⟨a', hab'⟩ := hsnd' b
    have h1' : ((a * a'⁻¹, 1) : P₁ × P₂) ∈ R := (hmemK _).mp (h1 ▸ Subgroup.mem_top _)
    simpa using R.mul_mem h1' hab'

noncomputable def prodTopBotEquiv :
    ↥((⊤ : Subgroup P₁).prod (⊥ : Subgroup P₂)) ≃* P₁ :=
  MulEquiv.ofBijective ((MonoidHom.fst P₁ P₂).comp (Subgroup.subtype _))
    ⟨fun x y hxy => by
      have hx := (Subgroup.mem_prod.mp x.2).2
      have hy := (Subgroup.mem_prod.mp y.2).2
      rw [Subgroup.mem_bot] at hx hy
      exact Subtype.ext (Prod.ext hxy (hx.trans hy.symm)),
    fun a => ⟨⟨(a, 1), Subgroup.mem_prod.mpr ⟨Subgroup.mem_top a, Subgroup.one_mem _⟩⟩, rfl⟩⟩

noncomputable def prodBotTopEquiv :
    ↥((⊥ : Subgroup P₁).prod (⊤ : Subgroup P₂)) ≃* P₂ :=
  MulEquiv.ofBijective ((MonoidHom.snd P₁ P₂).comp (Subgroup.subtype _))
    ⟨fun x y hxy => by
      have hx := (Subgroup.mem_prod.mp x.2).1
      have hy := (Subgroup.mem_prod.mp y.2).1
      rw [Subgroup.mem_bot] at hx hy
      exact Subtype.ext (Prod.ext (hx.trans hy.symm) hxy),
    fun b => ⟨⟨(1, b), Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, Subgroup.mem_top b⟩⟩, rfl⟩⟩

theorem prod_top_bot_inf_bot_top :
    (⊤ : Subgroup P₁).prod (⊥ : Subgroup P₂) ⊓ (⊥ : Subgroup P₁).prod (⊤ : Subgroup P₂) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf, Subgroup.mem_prod, Subgroup.mem_prod, Subgroup.mem_bot,
    Subgroup.mem_bot] at hx
  rw [Subgroup.mem_bot]
  exact Prod.ext hx.2.1 hx.1.2

theorem prod_top_bot_sup_bot_top :
    (⊤ : Subgroup P₁).prod (⊥ : Subgroup P₂) ⊔ (⊥ : Subgroup P₁).prod (⊤ : Subgroup P₂) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨a, b⟩ -
  have : ((a, b) : P₁ × P₂) = (a, 1) * (1, b) := by simp
  rw [this]
  exact Subgroup.mul_mem_sup (Subgroup.mem_prod.mpr ⟨Subgroup.mem_top a, Subgroup.one_mem _⟩)
    (Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, Subgroup.mem_top b⟩)

end Prod

section L2Sq

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19 (IsZModSq)

variable {P₁ P₂ : Type} [Group P₁] [Group P₂] [Finite P₁] [Finite P₂]

theorem isSimpleGroup_of_isL2 {Y : Type} [Group Y] {n : ℕ} (hn : 2 ≤ n) (hY : IsL2 Y n) :
    IsSimpleGroup Y := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := exists_sl2_of_isL2 hY
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have := CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup h4
  exact e.isSimpleGroup

theorem center_eq_bot_of_isL2 {Y : Type} [Group Y] {n : ℕ} (hY : IsL2 Y n) :
    Subgroup.center Y = ⊥ := by
  obtain ⟨F, _, _, _, -, ⟨e⟩⟩ := exists_sl2_of_isL2 hY
  rw [eq_bot_iff]
  intro d hd
  have hd' : e d ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff] at hd ⊢
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hd g']
  rw [center_sl2_eq_bot, Subgroup.mem_bot] at hd'
  rw [Subgroup.mem_bot]
  exact e.injective (hd'.trans (map_one e).symm)

private theorem pow_eq_one_of_isZModSq {X : Type} [Group X] {T : Subgroup X} {n : ℕ}
    (hT : IsZModSq T n)
    {t : X} (ht : t ∈ T) : t ^ (2 ^ n - 1) = 1 := by
  obtain ⟨e⟩ := hT
  have hx : ∀ {m : ℕ} (z : Multiplicative (ZMod m × ZMod m)), z ^ m = 1 := fun z => by
    rw [← toAdd_eq_zero, toAdd_pow]
    ext <;> simp
  have h1 : (⟨t, ht⟩ : T) ^ (2 ^ n - 1) = 1 :=
    e.injective (by rw [map_pow, hx (e ⟨t, ht⟩), map_one])
  simpa using congrArg Subtype.val h1

theorem perfect_of_l2sq {n : ℕ} (hn : 2 ≤ n)
    (h₁ : IsL2 P₁ n) (h₂ : IsL2 P₂ n) {T : Subgroup (P₁ × P₂)} (hT : IsZModSq T n)
    {R : Subgroup (P₁ × P₂)} (hR : ⁅R, R⁆ = R)
    (hTR : T ≤ Subgroup.normalizer (R : Set (P₁ × P₂))) :
    R = ⊥ ∨ R = (⊤ : Subgroup P₁).prod ⊥ ∨ R = (⊥ : Subgroup P₁).prod ⊤ ∨ R = ⊤ := by
  set S₁ : Subgroup (P₁ × P₂) := (⊤ : Subgroup P₁).prod (⊥ : Subgroup P₂) with hS₁def
  set S₂ : Subgroup (P₁ × P₂) := (⊥ : Subgroup P₁).prod (⊤ : Subgroup P₂) with hS₂def
  have hS₁n : S₁.Normal := by rw [hS₁def, ← MonoidHom.ker_snd]; exact MonoidHom.normal_ker _
  have hS₂n : S₂.Normal := by rw [hS₂def, ← MonoidHom.ker_fst]; exact MonoidHom.normal_ker _
  have hL₁ : IsL2 S₁ n := CFSG.Blueprint.LieModel.of_mulEquiv prodTopBotEquiv.symm h₁
  have hL₂ : IsL2 S₂ n := CFSG.Blueprint.LieModel.of_mulEquiv prodBotTopEquiv.symm h₂
  have hS : (IsL2 S₁ n ∧ IsL2 S₂ n) ∨ (IsSz S₁ n ∧ IsSz S₂ n) := Or.inl ⟨hL₁, hL₂⟩
  obtain ⟨hc₁, hc₂, -⟩ := S19.torus_eq_sup_inf_of_prod hn hT S₁ S₂ hS₁n hS₂n
    prod_top_bot_inf_bot_top prod_top_bot_sup_bot_top hS
  obtain ⟨hC₁, hC₂⟩ := S19.inf_eq_centralizer_inf_of_prod hn hT S₁ S₂ hS₁n hS₂n
    prod_top_bot_inf_bot_top prod_top_bot_sup_bot_top hS
  have hq1 : 1 < 2 ^ n - 1 := by
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨a, haTS, ha1⟩ : ∃ a ∈ T ⊓ S₁, a ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : T ⊓ S₁ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hno
    rw [hbot, Subgroup.card_bot] at hc₁
    omega
  obtain ⟨b, hbTS, hb1⟩ : ∃ b ∈ T ⊓ S₂, b ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : T ⊓ S₂ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hno
    rw [hbot, Subgroup.card_bot] at hc₂
    omega
  have ha2 : a.2 = 1 := by
    have := (Subgroup.mem_prod.mp haTS.2).2
    rwa [Subgroup.mem_bot] at this
  have hb1' : b.1 = 1 := by
    have := (Subgroup.mem_prod.mp hbTS.2).1
    rwa [Subgroup.mem_bot] at this
  have hd₁ : a.1 ≠ 1 := fun h => ha1 (Prod.ext h ha2)
  have hd₂ : b.2 ≠ 1 := fun h => hb1 (Prod.ext hb1' h)
  have hpa : a.1 ^ (2 ^ n - 1) = 1 := by
    have := pow_eq_one_of_isZModSq hT haTS.1
    rw [Prod.ext_iff] at this
    simpa using this.1
  have hpb : b.2 ^ (2 ^ n - 1) = 1 := by
    have := pow_eq_one_of_isZModSq hT hbTS.1
    rw [Prod.ext_iff] at this
    simpa using this.2
  have hP₁ : ⁅R.map (MonoidHom.fst P₁ P₂), R.map (MonoidHom.fst P₁ P₂)⁆ =
      R.map (MonoidHom.fst P₁ P₂) := by rw [← Subgroup.map_commutator, hR]
  have hP₂ : ⁅R.map (MonoidHom.snd P₁ P₂), R.map (MonoidHom.snd P₁ P₂)⁆ =
      R.map (MonoidHom.snd P₁ P₂) := by rw [← Subgroup.map_commutator, hR]
  have hN₁ : Subgroup.centralizer ({a.1} : Set P₁) ≤
      Subgroup.normalizer ((R.map (MonoidHom.fst P₁ P₂) : Subgroup P₁) : Set P₁) := by
    intro c hc
    have hcS : ((c, 1) : P₁ × P₂) ∈ Subgroup.centralizer ({a} : Set (P₁ × P₂)) ⊓ S₁ := by
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
        Subgroup.mem_prod.mpr ⟨Subgroup.mem_top c, Subgroup.one_mem _⟩⟩
      have hca := Subgroup.mem_centralizer_singleton_iff.mp hc
      exact Prod.ext hca (by simp [ha2])
    rw [← hC₁ a haTS ha1] at hcS
    exact Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ (hTR hcS.1))
  have hN₂ : Subgroup.centralizer ({b.2} : Set P₂) ≤
      Subgroup.normalizer ((R.map (MonoidHom.snd P₁ P₂) : Subgroup P₂) : Set P₂) := by
    intro c hc
    have hcS : ((1, c) : P₁ × P₂) ∈ Subgroup.centralizer ({b} : Set (P₁ × P₂)) ⊓ S₂ := by
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
        Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, Subgroup.mem_top c⟩⟩
      have hcb := Subgroup.mem_centralizer_singleton_iff.mp hc
      exact Prod.ext (by simp [hb1']) hcb
    rw [← hC₂ b hbTS hb1] at hcS
    exact Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ (hTR hcS.1))
  have hQ₁ := perfect_eq_bot_or_top_of_isL2 hn h₁ hd₁ hpa hP₁ hN₁
  have hQ₂ := perfect_eq_bot_or_top_of_isL2 hn h₂ hd₂ hpb hP₂ hN₂
  have hfst : ∀ r ∈ R, r.1 ∈ R.map (MonoidHom.fst P₁ P₂) := fun r hr => ⟨r, hr, rfl⟩
  have hsnd : ∀ r ∈ R, r.2 ∈ R.map (MonoidHom.snd P₁ P₂) := fun r hr => ⟨r, hr, rfl⟩
  rcases hQ₁ with h1 | h1 <;> rcases hQ₂ with h2 | h2
  · left
    rw [eq_bot_iff]
    intro r hr
    have e1 := hfst r hr
    have e2 := hsnd r hr
    rw [h1, Subgroup.mem_bot] at e1
    rw [h2, Subgroup.mem_bot] at e2
    exact (Subgroup.mem_bot).mpr (Prod.ext e1 e2)
  · right; right; left
    apply le_antisymm
    · intro r hr
      have e1 := hfst r hr
      rw [h1, Subgroup.mem_bot] at e1
      exact Subgroup.mem_prod.mpr ⟨(Subgroup.mem_bot).mpr e1, Subgroup.mem_top _⟩
    · rintro ⟨x, y⟩ hxy
      have hx1 : x = 1 := (Subgroup.mem_bot).mp (Subgroup.mem_prod.mp hxy).1
      have hy : y ∈ R.map (MonoidHom.snd P₁ P₂) := h2 ▸ Subgroup.mem_top y
      obtain ⟨r, hr, hry⟩ := Subgroup.mem_map.mp hy
      have e1 := hfst r hr
      rw [h1, Subgroup.mem_bot] at e1
      have : r = (x, y) := Prod.ext (e1.trans hx1.symm) hry
      exact this ▸ hr
  · right; left
    apply le_antisymm
    · intro r hr
      have e2 := hsnd r hr
      rw [h2, Subgroup.mem_bot] at e2
      exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, (Subgroup.mem_bot).mpr e2⟩
    · rintro ⟨x, y⟩ hxy
      have hy1 : y = 1 := (Subgroup.mem_bot).mp (Subgroup.mem_prod.mp hxy).2
      have hx : x ∈ R.map (MonoidHom.fst P₁ P₂) := h1 ▸ Subgroup.mem_top x
      obtain ⟨r, hr, hrx⟩ := Subgroup.mem_map.mp hx
      have e2 := hsnd r hr
      rw [h2, Subgroup.mem_bot] at e2
      have : r = (x, y) := Prod.ext hrx (e2.trans hy1.symm)
      exact this ▸ hr
  · right; right; right
    have := isSimpleGroup_of_isL2 hn h₁
    have hZ : a.1 ∉ Subgroup.center P₁ := by
      rw [center_eq_bot_of_isL2 h₁, Subgroup.mem_bot]
      exact hd₁
    have haN : ((a.1, 1) : P₁ × P₂) ∈ Subgroup.normalizer (R : Set (P₁ × P₂)) := by
      have : ((a.1, 1) : P₁ × P₂) = a := Prod.ext rfl ha2.symm
      rw [this]
      exact hTR haTS.1
    exact eq_top_of_fst_snd_eq_top h1 h2 hZ haN

end L2Sq

section Generic

open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem isQuasisimple_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hZ : Subgroup.center G = ⊥) : CFSG.Open.IsQuasisimple G := by
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_pair_ne G
      have htop : Subgroup.center G = ⊤ := by
        rw [eq_top_iff]
        intro z _
        rw [Subgroup.mem_center_iff]
        intro g
        have hc : ⁅g, z⁆ ∈ commutator G := by
          rw [commutator_def]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top z)
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
        exact hc
      have hab' : a = b := by
        have ha : a ∈ Subgroup.center G := htop ▸ Subgroup.mem_top a
        have hb : b ∈ Subgroup.center G := htop ▸ Subgroup.mem_top b
        rw [hZ, Subgroup.mem_bot] at ha hb
        rw [ha, hb]
      exact hab hab'
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup

theorem eq_bot_of_normal_isPGroup_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hG : ¬ IsPGroup 2 G) {P : Subgroup G} (hP : P.Normal) (h2 : IsPGroup 2 P) : P = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h | h
  · exact h
  · exfalso
    subst h
    exact hG (h2.of_equiv Subgroup.topEquiv)

theorem not_isPGroup_two_of_isL2 {Y : Type} [Group Y] {n : ℕ} (hn : 2 ≤ n) (hY : IsL2 Y n) :
    ¬ IsPGroup 2 Y := by
  intro h2
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := exists_sl2_of_isL2 hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsPGroup 2 SL(2, F) := h2.of_equiv e
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  rw [CFSG.CGT.Timmesfeld75.card_sl2, hF] at hk
  have hdvd : (2 ^ n) ^ 2 - 1 ∣ 2 ^ k := ⟨2 ^ n, by rw [← hk]; ring⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hodd : Odd ((2 ^ n) ^ 2 - 1) := by
    have h16 : 16 ≤ (2 ^ n) ^ 2 := by nlinarith
    have heven : Even ((2 ^ n) ^ 2) := by
      rw [← pow_mul]
      exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    obtain ⟨m, hm⟩ := heven
    exact ⟨m - 1, by omega⟩
  rw [hj] at hodd
  rcases j with _ | j
  · rw [pow_zero] at hj
    have h16 : 16 ≤ (2 ^ n) ^ 2 := by nlinarith
    omega
  · exact (Nat.not_even_iff_odd.mpr hodd) ⟨2 ^ j, by ring⟩

variable {P₁ P₂ : Type} [Group P₁] [Group P₂]

theorem not_isQuasisimple_prod [Nontrivial P₁] [Nontrivial P₂]
    (h₁ : Subgroup.center P₁ = ⊥) (h₂ : Subgroup.center P₂ = ⊥) :
    ¬ CFSG.Open.IsQuasisimple (P₁ × P₂) := by
  rintro ⟨-, hs⟩
  have hZ : Subgroup.center (P₁ × P₂) = ⊥ := by
    rw [Subgroup.center_prod, h₁, h₂, Subgroup.bot_prod_bot]
  have : IsSimpleGroup (P₁ × P₂) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  have hN : ((⊤ : Subgroup P₁).prod (⊥ : Subgroup P₂)).Normal := by
    rw [← MonoidHom.ker_snd]; exact MonoidHom.normal_ker _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((⊤ : Subgroup P₁).prod (⊥ : Subgroup P₂)) with h | h
  · obtain ⟨a, ha⟩ := exists_ne (1 : P₁)
    have hmem : ((a, 1) : P₁ × P₂) ∈ (⊤ : Subgroup P₁).prod (⊥ : Subgroup P₂) :=
      Subgroup.mem_prod.mpr ⟨Subgroup.mem_top a, Subgroup.one_mem _⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact ha (congrArg Prod.fst hmem)
  · obtain ⟨b, hb⟩ := exists_ne (1 : P₂)
    have hmem : ((1, b) : P₁ × P₂) ∈ (⊤ : Subgroup P₁).prod (⊥ : Subgroup P₂) :=
      h ▸ Subgroup.mem_top _
    have := (Subgroup.mem_prod.mp hmem).2
    rw [Subgroup.mem_bot] at this
    exact hb this

theorem eq_bot_of_normal_isPGroup_prod [IsSimpleGroup P₁] [IsSimpleGroup P₂]
    (h₁ : ¬ IsPGroup 2 P₁) (h₂ : ¬ IsPGroup 2 P₂) {Q : Subgroup (P₁ × P₂)} (hQ : Q.Normal)
    (h2 : IsPGroup 2 Q) : Q = ⊥ := by
  have e₁ := eq_bot_of_normal_isPGroup_of_simple h₁
    (hQ.map (MonoidHom.fst P₁ P₂) Prod.fst_surjective) (h2.map _)
  have e₂ := eq_bot_of_normal_isPGroup_of_simple h₂
    (hQ.map (MonoidHom.snd P₁ P₂) Prod.snd_surjective) (h2.map _)
  rw [eq_bot_iff]
  intro x hx
  have hx₁ : x.1 ∈ Q.map (MonoidHom.fst P₁ P₂) := ⟨x, hx, rfl⟩
  have hx₂ : x.2 ∈ Q.map (MonoidHom.snd P₁ P₂) := ⟨x, hx, rfl⟩
  rw [e₁, Subgroup.mem_bot] at hx₁
  rw [e₂, Subgroup.mem_bot] at hx₂
  exact Subgroup.mem_bot.mpr (Prod.ext hx₁ hx₂)

end Generic

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS

end
