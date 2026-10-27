module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.NatAPI
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.QuadraticFour
public import CFSG.Quasithin.EmptyFaithful.SzF53B3NGeo
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveA5

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem relIndex_sup_le_natCard {X L : Subgroup G} (hX : X ≤ Subgroup.normalizer (L : Set G)) :
    L.relIndex (X ⊔ L) ≤ Nat.card X := by
  let NG : Subgroup G := Subgroup.normalizer (L : Set G)
  have hKleNG : L ≤ NG := Subgroup.le_normalizer
  have hXLleNG : X ⊔ L ≤ NG := sup_le hX hKleNG
  let : (L.subgroupOf NG).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (H := L) (K := NG) hKleNG).2 le_rfl
  have h1 : L.relIndex (X ⊔ L) = (X ⊓ L).relIndex X := by
    calc L.relIndex (X ⊔ L)
        = (L.subgroupOf NG).relIndex ((X ⊔ L).subgroupOf NG) :=
          (Subgroup.relIndex_subgroupOf (H := L) (K := X ⊔ L) (L := NG) hXLleNG).symm
      _ = (L.subgroupOf NG).relIndex ((X.subgroupOf NG) ⊔ (L.subgroupOf NG)) := by
          rw [Subgroup.subgroupOf_sup (A := X) (A' := L) (B := NG) hX hKleNG]
      _ = (L.subgroupOf NG).relIndex (X.subgroupOf NG) :=
          Subgroup.relIndex_sup_right (H := X.subgroupOf NG) (K := L.subgroupOf NG)
      _ = ((X.subgroupOf NG) ⊓ (L.subgroupOf NG)).relIndex (X.subgroupOf NG) :=
          (Subgroup.inf_relIndex_left (H := X.subgroupOf NG) (K := L.subgroupOf NG)).symm
      _ = ((X ⊓ L).subgroupOf NG).relIndex (X.subgroupOf NG) := by
          rw [show (X.subgroupOf NG) ⊓ (L.subgroupOf NG) = (X ⊓ L).subgroupOf NG by
            ext x; simp [Subgroup.mem_subgroupOf]]
      _ = (X ⊓ L).relIndex X :=
          Subgroup.relIndex_subgroupOf (H := X ⊓ L) (K := X) (L := NG) hX
  rw [h1]
  exact Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card _ _)

theorem relIndex_centralizer_le_natCard {V Z : Subgroup G} {x : G}
    (hZ : ∀ y ∈ V, ∀ z ∈ Z, y * z = z * y) (hZa : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z)
    (hc : ∀ y ∈ V, ⁅y, x⁆ ∈ Z) :
    (Subgroup.centralizer {x} ⊓ V).relIndex V ≤ Nat.card Z := by
  let φ : ↥V →* ↥Z :=
    { toFun := fun y => ⟨⁅(y : G), x⁆, hc y y.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro y y'
        ext
        have h1 : ⁅(y : G) * y', x⁆ = (y : G) * ⁅(y' : G), x⁆ * (y : G)⁻¹ * ⁅(y : G), x⁆ := by
          simp [commutatorElement_def, mul_assoc]
        have h2 := hZ y y.2 _ (hc y' y'.2)
        have h3 : (y : G) * ⁅(y' : G), x⁆ * (y : G)⁻¹ = ⁅(y' : G), x⁆ := by
          rw [h2]; simp
        have h4 := hZa _ (hc y' y'.2) _ (hc y y.2)
        simp only [Subgroup.coe_mul]
        rw [h1, h3, h4] }
  have hker : φ.ker = (Subgroup.centralizer {x} ⊓ V).subgroupOf V := by
    ext y
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h
      have h' : ⁅(y : G), x⁆ = 1 := congrArg Subtype.val h
      exact ⟨((commutatorElement_eq_one_iff_mul_comm).mp h').symm, y.2⟩
    · rintro ⟨h, -⟩
      ext
      exact (commutatorElement_eq_one_iff_mul_comm).mpr h.symm
  have := Subgroup.index_ker φ
  unfold Subgroup.relIndex
  rw [← hker, this]
  exact Nat.card_le_card_of_injective (fun a : φ.range => (a : ↥Z)) Subtype.val_injective

theorem commutator_sup_le_of {X A L : Subgroup G} (hXL : X ≤ Subgroup.normalizer (L : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hXA : ⁅X, A⁆ ≤ L) :
    ⁅X ⊔ L, A⁆ ≤ L := by
  have hn : ∀ {g : G}, g ∈ Subgroup.normalizer (L : Set G) → ∀ {h : G}, h ∈ L → g * h * g⁻¹ ∈ L :=
    fun hg h hh => (Subgroup.mem_normalizer_iff.mp hg h).mp hh
  have hn' : ∀ {g : G}, g ∈ Subgroup.normalizer (L : Set G) → ∀ {h : G}, h ∈ L →
      g⁻¹ * h * g ∈ L := by
    intro g hg h hh
    have := hn (inv_mem hg) hh
    simpa using this
  let Q : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer (L : Set G) ∧ ∀ a ∈ A, ⁅g, a⁆ ∈ L}
      mul_mem' := by
        rintro g g' ⟨hg, hg1⟩ ⟨hg', hg1'⟩
        refine ⟨mul_mem hg hg', fun a ha => ?_⟩
        have : ⁅g * g', a⁆ = g * ⁅g', a⁆ * g⁻¹ * ⁅g, a⁆ := by
          simp [commutatorElement_def, mul_assoc]
        rw [this]
        exact mul_mem (hn hg (hg1' a ha)) (hg1 a ha)
      one_mem' := ⟨one_mem _, fun a ha => by simp⟩
      inv_mem' := by
        rintro g ⟨hg, hg1⟩
        refine ⟨inv_mem hg, fun a ha => ?_⟩
        have h1 := inv_mem (hg1 a ha)
        have h2 := hn' hg h1
        have : g⁻¹ * ⁅g, a⁆⁻¹ * g = ⁅g⁻¹, a⁆ := by
          simp [commutatorElement_def, mul_assoc]
        rwa [this] at h2 }
  have hXQ : X ≤ Q := fun x hx =>
    ⟨hXL hx, fun a ha => hXA (Subgroup.commutator_mem_commutator hx ha)⟩
  have hLQ : L ≤ Q := fun l hl => by
    refine ⟨Subgroup.le_normalizer hl, fun a ha => ?_⟩
    have : ⁅l, a⁆ = l * (a * l⁻¹ * a⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    refine mul_mem hl ?_
    have h3 := hn (hAL ha) (inv_mem hl)
    simpa [mul_assoc] using h3
  rw [Subgroup.commutator_le]
  intro g hg a ha
  exact (sup_le hXQ hLQ hg).2 a ha

theorem isElemAbelian_map_subgroupOf {K E : Subgroup G} (hE : IsElemAbelian 2 E) {L : Type*} [Group L]
    (φ : ↥K →* L) : IsElemAbelian 2 ((E.subgroupOf K).map φ) := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩⟩ ⟨_, ⟨b, hb, rfl⟩⟩
    have h := CFSG.Quasithin.F53B3.N37.elemAbelian_comm hE (a := (a : G)) (b := (b : G)) (Subgroup.mem_subgroupOf.mp ha) (Subgroup.mem_subgroupOf.mp hb)
    apply Subtype.ext
    show φ a * φ b = φ b * φ a
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext h)
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow]
    have := hE.2 (a : G) (Subgroup.mem_subgroupOf.mp ha)
    convert map_one φ
    exact Subtype.ext this

theorem relIndex_ne_zero' (A B : Subgroup G) : A.relIndex B ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

theorem commutator_le_of_le' {A B T : Subgroup G} (hA : A ≤ T) (hB : B ≤ T) : ⁅A, B⁆ ≤ T := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have : ⁅a, b⁆ = a * b * a⁻¹ * b⁻¹ := rfl
  rw [this]
  exact mul_mem (mul_mem (mul_mem (hA ha) (hB hb)) (inv_mem (hA ha))) (inv_mem (hB hb))

theorem card_cases_of_elemAbelian_perm {E : Subgroup (Equiv.Perm (Fin 5))}
    (hE : IsElemAbelian 2 E) : Nat.card E = 1 ∨ Nat.card E = 2 ∨ Nat.card E = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have h4 := CFSG.ComponentClassification.RankTwoAltFive.card_le_four_of_elemAbelian_perm hE
  rw [hk] at h4 ⊢
  have hk2 : k ≤ 2 := by
    by_contra h
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> simp

namespace Ctx
variable {α β α' : Geo H M} (C : Ctx H M S α β α')
include C

theorem Vn_beta_le_stab : Vn β ≤ stab α' :=
  C.Vn_le_stab_of_dist C.vtype_beta (by have := C.hc.dist_eq'; omega)

theorem Vn_alpha'_le_stab : Vn α' ≤ stab β :=
  C.Vn_le_stab_of_dist C.vtype_alpha' (by have := C.hc.dist_eq'; rw [CosetGeom.dist_comm]; omega)

theorem exists_Zalpha_not_Qalpha' : ∃ x ∈ Zv α, x ∉ Qv α' := by
  by_contra h
  exact C.hc.not_le fun x hx => by_contra fun hn => h ⟨x, hx, hn⟩

theorem Zv_alpha_le_Vn_beta : Zv α ≤ Vn β :=
  CFSG.Quasithin.F53B3.N37.Zv_le_Vn_of_adj C.hc.adj.symm

theorem Vn_le_Qv_imp {δ δ' : Geo H M} (hδ : vtype δ = false) (hδ' : vtype δ' = false)
    (hd : CosetGeom.dist δ δ' + 1 ≤ bMin H M) (hle : Vn δ' ≤ Qv δ) {x : G} (hx : x ∈ Vn δ) :
    x ∈ Qv δ' := by
  by_contra hxQ
  have hxs : x ∈ stab δ' := C.Vn_le_stab_of_dist hδ hd hx
  have h4 := C.four_le_relIndex_commSec hδ' hxs hxQ
  have hZs : Zv δ ≤ stab δ' := C.Zv_le_stab_of_dist_le hδ (by omega)
  have hcomm : ⁅Vn δ', Subgroup.zpowers x⁆ ≤ Zv δ := by
    rw [← C.comm_Vn_Qv_eq hδ]
    calc ⁅Vn δ', Subgroup.zpowers x⁆ ≤ ⁅Qv δ, Vn δ⁆ :=
          Subgroup.commutator_mono hle ((Subgroup.zpowers_le).2 hx)
      _ = ⁅Vn δ, Qv δ⁆ := Subgroup.commutator_comm _ _
  have hnorm : ⁅Vn δ', Subgroup.zpowers x⁆ ≤ Subgroup.normalizer (F53B3.Cv δ' : Set G) :=
    hcomm.trans (hZs.trans (CFSG.Quasithin.F53B3.N37.stab_le_normalizer_Cv δ'))
  have h5 := relIndex_sup_le_natCard hnorm
  have h6 : Nat.card ↥⁅Vn δ', Subgroup.zpowers x⁆ ≤ 2 :=
    (Subgroup.card_le_of_le hcomm).trans (C.card_Zv_false hδ).le
  exact absurd (h4.trans (h5.trans h6)) (by norm_num)

theorem not_Vn_alpha'_le_Qv_beta : ¬ Vn α' ≤ Qv β := by
  intro hle
  obtain ⟨x, hxZ, hxQ⟩ := C.exists_Zalpha_not_Qalpha'
  exact hxQ (C.Vn_le_Qv_imp C.vtype_beta C.vtype_alpha'
    (by have := C.hc.dist_eq'; omega) hle (C.Zv_alpha_le_Vn_beta hxZ))

theorem not_Vn_beta_le_Qv_alpha' : ¬ Vn β ≤ Qv α' := by
  intro hle
  obtain ⟨x, hx, hxQ⟩ := Set.not_subset.mp C.not_Vn_alpha'_le_Qv_beta
  exact hxQ (C.Vn_le_Qv_imp C.vtype_alpha' C.vtype_beta
    (by have := C.hc.dist_eq'; rw [CosetGeom.dist_comm]; omega) hle hx)

theorem card_map_theta {δ : Geo H M} {θ : ↥(stab δ) →* Equiv.Perm (Fin 5)}
    (hθk : θ.ker = (Qv δ).subgroupOf (stab δ)) {A : Subgroup G} (hA : A ≤ stab δ) :
    Nat.card ((A.subgroupOf (stab δ)).map θ) = (Qv δ).relIndex A := by
  rw [← Subgroup.relIndex_ker, hθk]
  exact Subgroup.relIndex_subgroupOf hA

theorem relIndex_ne_two_of_eq_four {δ δ' : Geo H M} (hδ : vtype δ = false)
    (hδ' : vtype δ' = false) (hd : CosetGeom.dist δ δ' + 1 = bMin H M)
    (h4 : (Qv δ).relIndex (Vn δ') = 4) : (Qv δ').relIndex (Vn δ) ≠ 2 := by
  intro h2
  obtain ⟨hN, θ, βm, -, hθk, hsd⟩ := C.exists_secData hδ
  obtain ⟨-, hAK, -, hq0⟩ := hss114_d C.hA C.hb3 hd
  have hVδs : Vn δ ≤ stab δ :=
    (C.Vn_le_Qv_self hδ).trans (CFSG.Quasithin.F53B3.N37.Qv_le_stab_self δ)
  have hLX : F53B3.Cv δ ≤ Vn δ := inf_le_left
  have hstabN := CFSG.Quasithin.F53B3.N37.stab_le_normalizer_Cv (H := H) (M := M) δ
  have hXN : ⁅Vn δ, Vn δ'⁆ ≤ Subgroup.normalizer (F53B3.Cv δ : Set G) :=
    (commutator_le_of_le' hVδs hAK).trans hstabN
  have hAN : Vn δ' ≤ Subgroup.normalizer (F53B3.Cv δ : Set G) := hAK.trans hstabN
  have hquadC : ⁅commSec (Vn δ') (F53B3.Cv δ) (Vn δ), Vn δ'⁆ ≤ F53B3.Cv δ :=
    commutator_sup_le_of hXN hAN (by rw [hq0]; exact bot_le)
  have hq := (hsd.quadratic_iff hLX hAK).mp hquadC
  have hcard : Nat.card (((Vn δ').subgroupOf (stab δ)).map θ) = 4 := by
    rw [C.card_map_theta hθk hAK]; exact h4
  have hXN' : Vn δ ≤ Subgroup.normalizer (F53B3.Cv δ : Set G) := hVδs.trans hstabN
  have hZ : ∀ y ∈ Vn δ', ∀ z ∈ Zv δ', y * z = z * y := fun y hy z hz =>
    Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv C.hA δ' hz).2 y (C.Vn_le_Qv_self hδ' hy)
  have hZa : ∀ z ∈ Zv δ', ∀ z' ∈ Zv δ', z * z' = z' * z := fun z hz z' hz' =>
    CFSG.Quasithin.F53B3.N37.elemAbelian_comm (isElemAbelian_Zv C.hA δ') hz hz'
  have hF : ∀ x ∈ Vn δ, x ∈ Qv δ' → x ∈ fixSecIn (Vn δ') (F53B3.Cv δ) (Vn δ) := by
    intro x hxV hxQ
    have hc : ∀ y ∈ Vn δ', ⁅y, x⁆ ∈ Zv δ' := fun y hy => by
      rw [← C.comm_Vn_Qv_eq hδ']; exact Subgroup.commutator_mem_commutator hy hxQ
    have hidx := relIndex_centralizer_le_natCard hZ hZa hc
    rw [C.card_Zv_false hδ'] at hidx
    obtain ⟨y, hyB, hyQ⟩ : ∃ y ∈ Subgroup.centralizer {x} ⊓ Vn δ', y ∉ Qv δ := by
      by_contra hno
      push Not at hno
      have hle : Subgroup.centralizer {x} ⊓ Vn δ' ≤ Qv δ ⊓ Vn δ' := fun y hy => ⟨hno y hy, hy.2⟩
      have hne := relIndex_ne_zero' (Subgroup.centralizer {x} ⊓ Vn δ') (Vn δ')
      have h5 := Subgroup.relIndex_le_of_le_left hle hne
      rw [Subgroup.inf_relIndex_right, h4] at h5
      omega
    have hya : y ∈ Vn δ' := hyB.2
    have hys : y ∈ stab δ := hAK hya
    have ha1 : θ ⟨y, hys⟩ ≠ 1 := by
      intro h
      have : (⟨y, hys⟩ : ↥(stab δ)) ∈ θ.ker := h
      rw [hθk, Subgroup.mem_subgroupOf] at this
      exact hyQ this
    have haA : θ ⟨y, hys⟩ ∈ ((Vn δ').subgroupOf (stab δ)).map θ :=
      ⟨⟨y, hys⟩, Subgroup.mem_subgroupOf.mpr hya, rfl⟩
    obtain ⟨-, hfix, hidx4⟩ := quadratic_four_nat hcard hq haA ha1
    have hzle : Subgroup.zpowers y ≤ Vn δ' := (Subgroup.zpowers_le).mpr hya
    have hzK : Subgroup.zpowers y ≤ stab δ := hzle.trans hAK
    have hxFy : x ∈ fixSecIn (Subgroup.zpowers y) (F53B3.Cv δ) (Vn δ) := by
      rw [CFSG.Quasithin.F53Mod.mem_fixSecIn_iff hXN']
      refine ⟨hxV, fun g hg => ?_⟩
      have hg' : g ∈ Subgroup.centralizer {x} := (Subgroup.zpowers_le.mpr hyB.1) hg
      have : x * g = g * x := Subgroup.mem_centralizer_iff.mp hg' x rfl
      have h1 : g * x * g⁻¹ * x⁻¹ = 1 := by
        rw [← this]; group
      rw [h1]; exact one_mem _
    have hmap : ((Subgroup.zpowers y).subgroupOf (stab δ)).map θ =
        Subgroup.zpowers (θ ⟨y, hys⟩) := by
      have : (Subgroup.zpowers y).subgroupOf (stab δ) = Subgroup.zpowers (⟨y, hys⟩ : ↥(stab δ)) := by
        ext z
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
        constructor
        · rintro ⟨k, hk⟩
          exact ⟨k, Subtype.ext (by simpa using hk)⟩
        · rintro ⟨k, rfl⟩
          exact ⟨k, by simp⟩
      rw [this, MonoidHom.map_zpowers]
    have hrFy : (fixSecIn (Subgroup.zpowers y) (F53B3.Cv δ) (Vn δ)).relIndex (Vn δ) = 4 := by
      rw [hsd.relIndex_fixSecIn hLX hzK, hmap, ← hfix, hidx4]
    have hrF : (fixSecIn (Vn δ') (F53B3.Cv δ) (Vn δ)).relIndex (Vn δ) = 4 := by
      rw [hsd.relIndex_fixSecIn hLX hAK, hidx4]
    have hFle : fixSecIn (Vn δ') (F53B3.Cv δ) (Vn δ) ≤
        fixSecIn (Subgroup.zpowers y) (F53B3.Cv δ) (Vn δ) := by
      intro z hz
      rw [CFSG.Quasithin.F53Mod.mem_fixSecIn_iff hXN'] at hz ⊢
      exact ⟨hz.1, fun g hg => hz.2 g (hzle hg)⟩
    have hFyX : fixSecIn (Subgroup.zpowers y) (F53B3.Cv δ) (Vn δ) ≤ Vn δ := by
      intro z hz
      exact ((CFSG.Quasithin.F53Mod.mem_fixSecIn_iff hXN').mp hz).1
    have hmul := Subgroup.relIndex_mul_relIndex (fixSecIn (Vn δ') (F53B3.Cv δ) (Vn δ))
      (fixSecIn (Subgroup.zpowers y) (F53B3.Cv δ) (Vn δ)) (Vn δ) hFle hFyX
    rw [hrF, hrFy] at hmul
    have h1 : (fixSecIn (Vn δ') (F53B3.Cv δ) (Vn δ)).relIndex
        (fixSecIn (Subgroup.zpowers y) (F53B3.Cv δ) (Vn δ)) = 1 := by omega
    exact (Subgroup.relIndex_eq_one.mp h1) hxFy
  have hD : (Qv δ' ⊓ Vn δ) ≤ fixSecIn (Vn δ') (F53B3.Cv δ) (Vn δ) :=
    fun x hx => hF x hx.2 hx.1
  have hne := relIndex_ne_zero' (Qv δ' ⊓ Vn δ) (Vn δ)
  have h5 := Subgroup.relIndex_le_of_le_left hD hne
  rw [Subgroup.inf_relIndex_right, h2] at h5
  have hrF : (fixSecIn (Vn δ') (F53B3.Cv δ) (Vn δ)).relIndex (Vn δ) = 4 := by
    rw [hsd.relIndex_fixSecIn hLX hAK]
    obtain ⟨a, haA, ha1⟩ : ∃ a ∈ ((Vn δ').subgroupOf (stab δ)).map θ, a ≠ 1 := by
      by_contra hno
      push Not at hno
      have hbot : ((Vn δ').subgroupOf (stab δ)).map θ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hno
      rw [hbot] at hcard
      simp at hcard
    exact (quadratic_four_nat hcard hq haA ha1).2.2
  omega

theorem relIndex_Qv_Vn_cases {δ δ' : Geo H M} (hδ : vtype δ = false)
    (hd : CosetGeom.dist δ δ' + 1 = bMin H M) :
    (Qv δ).relIndex (Vn δ') = 1 ∨ (Qv δ).relIndex (Vn δ') = 2 ∨ (Qv δ).relIndex (Vn δ') = 4 := by
  obtain ⟨hN, θ, βm, -, hθk, -⟩ := C.exists_secData hδ
  obtain ⟨-, hAK, -, -⟩ := hss114_d C.hA C.hb3 hd
  rw [← C.card_map_theta hθk hAK]
  exact card_cases_of_elemAbelian_perm
    (isElemAbelian_map_subgroupOf (isElemAbelian_Vn C.hA C.hb3 δ') θ)

theorem relIndex_Qv_Vn_eq :
    (Qv β).relIndex (Vn α') = (Qv α').relIndex (Vn β) ∧
      ((Qv β).relIndex (Vn α') = 2 ∨ (Qv β).relIndex (Vn α') = 4) := by
  have hd : CosetGeom.dist β α' + 1 = bMin H M := C.hc.dist_eq'
  have hd' : CosetGeom.dist α' β + 1 = bMin H M := by rw [CosetGeom.dist_comm]; exact hd
  have h1 : (Qv β).relIndex (Vn α') ≠ 1 := fun h =>
    C.not_Vn_alpha'_le_Qv_beta (Subgroup.relIndex_eq_one.mp h)
  have h2 : (Qv α').relIndex (Vn β) ≠ 1 := fun h =>
    C.not_Vn_beta_le_Qv_alpha' (Subgroup.relIndex_eq_one.mp h)
  have c1 := C.relIndex_Qv_Vn_cases C.vtype_beta hd
  have c2 := C.relIndex_Qv_Vn_cases C.vtype_alpha' hd'
  have e1 := C.relIndex_ne_two_of_eq_four C.vtype_beta C.vtype_alpha' hd
  have e2 := C.relIndex_ne_two_of_eq_four C.vtype_alpha' C.vtype_beta hd'
  omega

end Ctx
end CFSG.Quasithin.Kleidman.F53Hss36
