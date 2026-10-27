module

public import CFSG.Quasithin.Background.FFC12D
public import CFSG.Quasithin.Background.A3Structure312Embed
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace B69

theorem mem_normalizer_closure_of_gens {G : Type*} [Group G] {S : Set G} {g : G}
    (h1 : ∀ y ∈ S, g * y * g⁻¹ ∈ Subgroup.closure S)
    (h2 : ∀ y ∈ S, g⁻¹ * y * g ∈ Subgroup.closure S) :
    g ∈ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  have f1 : ∀ y ∈ Subgroup.closure S, g * y * g⁻¹ ∈ Subgroup.closure S := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact h1 x hx
    | one => simp
    | mul x y _ _ ihx ihy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact (Subgroup.closure S).mul_mem ihx ihy
    | inv x _ ih =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact (Subgroup.closure S).inv_mem ih
  have f2 : ∀ y ∈ Subgroup.closure S, g⁻¹ * y * g ∈ Subgroup.closure S := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact h2 x hx
    | one => simp
    | mul x y _ _ ihx ihy =>
      have : g⁻¹ * (x * y) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) := by group
      rw [this]
      exact (Subgroup.closure S).mul_mem ihx ihy
    | inv x _ ih =>
      have : g⁻¹ * x⁻¹ * g = (g⁻¹ * x * g)⁻¹ := by group
      rw [this]
      exact (Subgroup.closure S).inv_mem ih
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact f1 y
  · intro hy
    have := f2 _ hy
    simpa [mul_assoc] using this

theorem not_odd_card_quasisimple {G : Type*} [Group G] {L : Subgroup G} [Finite ↥L]
    (hL : CFSG.Open.IsQuasisimple ↥L) : ¬ Odd (Nat.card ↥L) := by
  intro hodd
  have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard ↥L hodd
  have hperf : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hL.1
  have hnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hL
  exact Group.IsPerfect.not_isSolvable ↥L hsolv

theorem mem_normalizer_of_commute_all {G : Type*} [Group G] {K : Subgroup G} {y : G}
    (h : ∀ z ∈ K, z * y = y * z) : y ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have e : y * z * y⁻¹ = z := by
      calc y * z * y⁻¹ = (z * y) * y⁻¹ := by rw [h z hz]
        _ = z := by group
    rw [e]
    exact hz
  · intro hz
    have hw := h _ hz
    have e : z = y * z * y⁻¹ :=
      calc z = y⁻¹ * ((y * z * y⁻¹) * y) := by group
        _ = y⁻¹ * (y * (y * z * y⁻¹)) := by rw [hw]
        _ = y * z * y⁻¹ := by group
    rw [e]
    exact hz

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem normalizer_le_M_of_component {X T M L : Subgroup (MulAut V)} (hmp : MinParabolic X T M)
    (hO2 : CFSG.Open.pCoreOf 2 X = ⊥) (hL : CFSG.Open.IsComponentOf L X)
    (hTL : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L) :
    L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V)) ≤ M := by
  set gens : Set (MulAut V) := {y | y ∈ T ∧ ∃ L' : Subgroup (MulAut V),
    CFSG.Open.IsComponentOf L' X ∧ y ∈ L'} with hgens
  set U : Subgroup (MulAut V) := Subgroup.closure gens with hU
  have hUT : U ≤ T := (Subgroup.closure_le T).2 fun y hy => hy.1
  have hUX : U ≤ X := hUT.trans hmp.isSylow.1
  have hU2 : IsPGroup 2 ↥U := hmp.isSylow.2.1.to_le hUT
  have hTn : T ≤ Subgroup.normalizer (U : Set (MulAut V)) := by
    intro t ht
    have htX : t ∈ X := hmp.isSylow.1 ht
    have htX' : t⁻¹ ∈ X := X.inv_mem htX
    refine mem_normalizer_closure_of_gens (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨hyT, L', hL', hyL'⟩ := hy
      refine Subgroup.subset_closure ⟨T.mul_mem (T.mul_mem ht hyT) (T.inv_mem ht),
        B6.conjSub t L', B113.isComponentOf_conj hL' htX, ?_⟩
      rw [B6.mem_conjSub]
      have : t⁻¹ * (t * y * t⁻¹) * t = y := by group
      rw [this]
      exact hyL'
    · obtain ⟨hyT, L', hL', hyL'⟩ := hy
      refine Subgroup.subset_closure ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hyT) ht,
        B6.conjSub t⁻¹ L', B113.isComponentOf_conj hL' htX', ?_⟩
      rw [B6.mem_conjSub]
      have : (t⁻¹)⁻¹ * (t⁻¹ * y * t) * t⁻¹ = y := by group
      rw [this]
      exact hyL'
  have hTLne : T ⊓ L ≠ ⊥ := by
    intro hbot
    have h := hTL.2.2
    rw [hbot, Subgroup.bot_subgroupOf, Subgroup.index_bot] at h
    exact not_odd_card_quasisimple hL.2.2 (Nat.odd_iff.2 (by omega))
  have hUne : U ≠ ⊥ := by
    intro hbot
    apply hTLne
    rw [eq_bot_iff]
    intro y hy
    have : y ∈ U := Subgroup.subset_closure ⟨hy.1, L, hL, hy.2⟩
    rw [hbot] at this
    exact this
  have hXn : ¬ X ≤ Subgroup.normalizer (U : Set (MulAut V)) := by
    intro hn
    have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUX hn hU2
    rw [hO2] at this
    exact hUne (le_bot_iff.1 this)
  set R : Subgroup (MulAut V) := X ⊓ Subgroup.normalizer (U : Set (MulAut V)) with hR
  have hTR : T ≤ R := le_inf hmp.isSylow.1 hTn
  have hRX : R < X := lt_of_le_of_ne inf_le_left (fun h => hXn (h ▸ inf_le_right))
  have hRM : R ≤ M := hmp.le_of_lt hTR hRX
  have key : ∀ c ∈ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V)),
      ∀ y ∈ gens, c * y * c⁻¹ ∈ U := by
    intro c hc y hy
    obtain ⟨hyT, L', hL', hyL'⟩ := hy
    by_cases hLL' : L = L'
    · subst hLL'
      have h1 : c * y * c⁻¹ ∈ T ⊓ L := (Subgroup.mem_normalizer_iff.1 hc.2 y).1 ⟨hyT, hyL'⟩
      exact Subgroup.subset_closure ⟨h1.1, L, hL, h1.2⟩
    · have hcomm : y * c = c * y := components_mul_comm_of_ne hL hL' hLL' y hyL' c hc.1
      have h1 : c * y * c⁻¹ = y := by
        calc c * y * c⁻¹ = (y * c) * c⁻¹ := by rw [hcomm]
          _ = y := by group
      rw [h1]
      exact Subgroup.subset_closure ⟨hyT, L', hL', hyL'⟩
  intro b hb
  apply hRM
  refine ⟨hL.1 hb.1, ?_⟩
  have hb' : b⁻¹ ∈ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V)) :=
    (L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V))).inv_mem hb
  exact mem_normalizer_closure_of_gens (key b hb) (fun y hy => by simpa using key b⁻¹ hb' y hy)

theorem not_component_le_M {X T M L : Subgroup (MulAut V)} (hmp : MinParabolic X T M)
    (hO2 : CFSG.Open.pCoreOf 2 X = ⊥) (hL : CFSG.Open.IsComponentOf L X) : ¬ L ≤ M := by
  intro hLM
  set gens : Set (MulAut V) := {y | ∃ x ∈ X, ∃ l ∈ L, y = x * l * x⁻¹} with hgens
  set Y : Subgroup (MulAut V) := Subgroup.closure gens with hY
  have hgenX : ∀ y ∈ gens, y ∈ X := by
    rintro _ ⟨x, hx, l, hl, rfl⟩
    exact X.mul_mem (X.mul_mem hx (hL.1 hl)) (X.inv_mem hx)
  have hYX : Y ≤ X := (Subgroup.closure_le X).2 hgenX
  have hLY : L ≤ Y := fun l hl => Subgroup.subset_closure ⟨1, X.one_mem, l, hl, by group⟩
  have hYn : X ≤ Subgroup.normalizer (Y : Set (MulAut V)) := by
    intro g hg
    refine mem_normalizer_closure_of_gens (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨x, hx, l, hl, rfl⟩ := hy
      exact Subgroup.subset_closure ⟨g * x, X.mul_mem hg hx, l, hl, by group⟩
    · obtain ⟨x, hx, l, hl, rfl⟩ := hy
      exact Subgroup.subset_closure ⟨g⁻¹ * x, X.mul_mem (X.inv_mem hg) hx, l, hl, by group⟩
  rcases hmp.le_kerIn_or_twoResidual_le hYX hYn with h1 | h2
  ·
    have hLJ : L ≤ kerIn M X := hLY.trans h1
    have hJ := hmp.isSylowTwoOf_pCoreOf_kerIn
    rw [hO2] at hJ
    have h3 := hJ.2.2
    rw [Subgroup.bot_subgroupOf, Subgroup.index_bot] at h3
    have hodd : Odd (Nat.card (kerIn M X)) := Nat.odd_iff.2 (by omega)
    exact not_odd_card_quasisimple hL.2.2 (hodd.of_dvd_nat (Subgroup.card_dvd_of_le hLJ))
  ·
    have hYcomp : ∀ L'' : Subgroup (MulAut V), CFSG.Open.IsComponentOf L'' X →
        Y ≤ Subgroup.normalizer (L'' : Set (MulAut V)) := by
      intro L'' hL''
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨x, hx, l, hl, rfl⟩
      have hL' : CFSG.Open.IsComponentOf (B6.conjSub x L) X := B113.isComponentOf_conj hL hx
      have hy : x * l * x⁻¹ ∈ B6.conjSub x L := by
        rw [B6.mem_conjSub]
        have : x⁻¹ * (x * l * x⁻¹) * x = l := by group
        rw [this]
        exact hl
      by_cases heq : B6.conjSub x L = L''
      · rw [heq] at hy
        exact Subgroup.le_normalizer hy
      · exact mem_normalizer_of_commute_all fun z hz =>
          components_mul_comm_of_ne hL' hL'' heq z hz _ hy
    have hconj : ∀ x ∈ X, ∃ b ∈ T, B6.conjSub x L = B6.conjSub b L := by
      intro x hx
      have hx' : x ∈ twoResidual X ⊔ T := by
        rw [← hmp.eq_twoResidual_sup]
        exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer
        (hmp.isSylow.1.trans (le_normalizer_twoResidual X))).1 hx'
      refine ⟨b, hb, ?_⟩
      have hLb : CFSG.Open.IsComponentOf (B6.conjSub b L) X :=
        B113.isComponentOf_conj hL (hmp.isSylow.1 hb)
      rw [B6.conjSub_mul, B6.conjSub_eq_self (hYcomp _ hLb (h2 ha))]
    have hYM : Y ≤ M := by
      refine (Subgroup.closure_le M).2 ?_
      rintro _ ⟨x, hx, l, hl, rfl⟩
      obtain ⟨b, hb, hxb⟩ := hconj x hx
      have hy : x * l * x⁻¹ ∈ B6.conjSub x L := by
        rw [B6.mem_conjSub]
        have : x⁻¹ * (x * l * x⁻¹) * x = l := by group
        rw [this]
        exact hl
      rw [hxb, B6.mem_conjSub] at hy
      have h4 : x * l * x⁻¹ = b * (b⁻¹ * (x * l * x⁻¹) * b) * b⁻¹ := by group
      rw [h4]
      exact M.mul_mem (M.mul_mem (hmp.le hb) (hLM hy)) (M.inv_mem (hmp.le hb))
    have hXM : X ≤ M := by
      rw [hmp.eq_twoResidual_sup]
      exact sup_le (h2.trans hYM) hmp.le
    exact absurd (lt_of_le_of_lt hXM hmp.maximal.1) (lt_irrefl _)

theorem asB69RankOneBorel_proved : AsB69RankOneBorel := by
  intro V _ _ hV X T M A L hH W hW hex
  obtain ⟨e, he, hnat⟩ := hex
  obtain ⟨-, hmp, hO2, -, -, hA, hL, hLA⟩ := hH
  have hTL : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    A312.isSylowTwoOf_inf_of_subnormal hL.2.1 hmp.isSylow
  apply le_antisymm
  · obtain ⟨K, hKf, hKfin, hK, π₀, hπ₀⟩ := hnat
    let π : ↥(StatedSL 2 K) →* ↥L := π₀
    have hπ : (FFModel.nat (StatedSL 2 K)).RealizesVia L W (W ⊓ fixV L) π := hπ₀
    let π' : Matrix.SpecialLinearGroup (Fin 2) K →* ↥L :=
      π.comp (specialLinearGroupEquivStatedSL 2 K).toMonoidHom
    have hπ's : Function.Surjective π' :=
      hπ.1.comp (specialLinearGroupEquivStatedSL 2 K).surjective
    set U : Subgroup ↥L := (T ⊓ L).subgroupOf L with hUdef
    set R : Subgroup ↥L := (M ⊓ L).subgroupOf L with hRdef
    have hUR : U ≤ R := fun x hx => ⟨hmp.le hx.1, hx.2⟩
    have hUp : IsPGroup 2 ↥U :=
      hTL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ L ≤ L)).symm
    have hUi : ¬ 2 ∣ U.index := hTL.2.2
    rcases overgroup_sylow_of_quotient_sl2 he hK π' hπ's hUp hUi hUR with h | h
    · exfalso
      apply not_component_le_M hmp hO2 hL
      intro x hx
      have : (⟨x, hx⟩ : ↥L) ∈ R := by rw [h]; trivial
      exact this.1
    · intro x hx
      have hxR : (⟨x, hx.2⟩ : ↥L) ∈ R := hx
      have hn := h hxR
      rw [Subgroup.mem_normalizer_iff] at hn
      have hxn : x ∈ Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V)) := by
        rw [Subgroup.mem_normalizer_iff]
        intro w
        constructor
        · intro hw
          exact (hn ⟨w, hw.2⟩).1 hw
        · intro hw
          have hwL : w ∈ L := by
            have h1 : x⁻¹ * (x * w * x⁻¹) * x ∈ L :=
              L.mul_mem (L.mul_mem (L.inv_mem hx.2) hw.2) hx.2
            have h2 : x⁻¹ * (x * w * x⁻¹) * x = w := by group
            rwa [h2] at h1
          exact (hn ⟨w, hwL⟩).2 hw
      exact ⟨hx.2, hxn⟩
  · intro x hx
    exact ⟨normalizer_le_M_of_component hmp hO2 hL hTL hx, hx.1⟩

end Main

end B69

end CFSG.Quasithin
