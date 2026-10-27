module

public import CFSG.Quasithin.Background.C124AsmFrattini

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped Pointwise MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem perfectCore_subgroupOf' {K L : Subgroup G} (hK : K ≤ L) :
    perfectCore (K.subgroupOf L) = (perfectCore K).subgroupOf L := by
  apply Subgroup.map_injective L.subtype_injective
  rw [map_perfectCore L.subtype (K.subgroupOf L), Subgroup.map_subgroupOf_eq_of_le hK,
    Subgroup.map_subgroupOf_eq_of_le ((perfectCore_le K).trans hK)]

theorem autI_perfectCore {V L K : Subgroup G} {hV : IsElemAbelian 2 V}
    (hL : L ≤ Subgroup.normalizer (V : Set G)) (hK : K ≤ L) :
    autI hV (perfectCore K) = perfectCore (autI hV K) := by
  rw [autI_eq_map_convHom hV hL ((perfectCore_le K).trans hK), autI_eq_map_convHom hV hL hK,
    ← perfectCore_subgroupOf' hK, map_perfectCore]

theorem isPGroup_autI {V P : Subgroup G} {hV : IsElemAbelian 2 V} (hP : IsPGroup 2 P) :
    IsPGroup 2 (autI hV P) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨⟨g, hgN⟩, hg, rfl⟩ := (mem_autI hV).1 hφ
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : (⟨g, hgN⟩ : Subgroup.normalizer (V : Set G)) ^ 2 ^ k = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hk)
  show (convI hV ⟨g, hgN⟩) ^ 2 ^ k = 1
  rw [← map_pow, h1, map_one]

theorem sl2_four_facts {H : Type*} [Group H] [Finite H] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) (e : H ≃* SL(2, F)) :
    IsSimpleGroup H ∧ Group.IsPerfect H ∧ Nat.card H = 60 ∧ ∃ a b : H, a * b ≠ b * a := by
  have hF4 : Nat.card F = 2 ^ 2 := by rw [hF]; norm_num
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by norm_num) hF4
  have h4 : 4 ≤ Nat.card F := by omega
  have hsimple : IsSimpleGroup SL(2, F) := C126.Nat.isSimpleGroup_sl2 h4
  have hsH : IsSimpleGroup H := e.isSimpleGroup
  have h60 : Nat.card H = 60 := by rw [Nat.card_congr e.toEquiv, L2.card_sl2_four hF]
  have hnc : ∃ a b : H, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have : IsMulCommutative H := ⟨⟨fun a b => hcon a b⟩⟩
    have hp := hsH.prime_card
    rw [h60] at hp
    norm_num at hp
  refine ⟨hsH, ?_, h60, hnc⟩
  rw [Group.isPerfect_def]
  rcases hsH.eq_bot_or_eq_top_of_normal (commutator H) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    have : ⁅a, b⁆ ∈ commutator H := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 this
  · exact h

omit [Finite G] in
theorem convI_eq_of_mul_inv_mem {V : Subgroup G} {hV : IsElemAbelian 2 V} {a b : G}
    (ha : a ∈ Subgroup.normalizer (V : Set G)) (hb : b ∈ Subgroup.normalizer (V : Set G))
    (h : a * b⁻¹ ∈ Subgroup.centralizer (V : Set G)) : convI hV ⟨a, ha⟩ = convI hV ⟨b, hb⟩ := by
  have h1 : convI hV (⟨a, ha⟩ * ⟨b, hb⟩⁻¹) = 1 := (convI_eq_one_iff hV _).2 h
  rw [map_mul, map_inv] at h1
  exact mul_inv_eq_one.1 h1

namespace EntryPlus

variable {X T V L R : Subgroup G} {m : ℕ} {hV : IsElemAbelian 2 V}
  (E : EntryPlus X T V L R m hV)

include E

theorem mem_normalizer_preI {Ys : Subgroup (MulAut (IntMod V hV))} {x : G} (hx : x ∈ X)
    (hxn : convI hV ⟨x, E.hXN hx⟩ ∈ Subgroup.normalizer (Ys : Set (MulAut (IntMod V hV)))) :
    x ∈ Subgroup.normalizer (preI hV L E.hLN Ys : Set G) := by
  have key : ∀ (y : G) (hy : y ∈ X), convI hV ⟨y, E.hXN hy⟩ ∈
      Subgroup.normalizer (Ys : Set (MulAut (IntMod V hV))) →
      ∀ z ∈ preI hV L E.hLN Ys, y * z * y⁻¹ ∈ preI hV L E.hLN Ys := by
    intro y hy hyn z hz
    obtain ⟨hzL, hzB⟩ := (mem_preI hV).1 hz
    have hyz : y * z * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (E.normal hy) z).1 hzL
    refine (mem_preI hV).2 ⟨hyz, ?_⟩
    have h1 : convHom hV L E.hLN ⟨y * z * y⁻¹, hyz⟩ =
        convI hV ⟨y, E.hXN hy⟩ * convHom hV L E.hLN ⟨z, hzL⟩ * (convI hV ⟨y, E.hXN hy⟩)⁻¹ := by
      rw [convHom_apply, convHom_apply, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h1]
    exact (Subgroup.mem_normalizer_iff.1 hyn _).1 hzB
  apply mem_normalizer_of_conj (key x hx hxn)
  have hxinv : convI hV ⟨x⁻¹, E.hXN (X.inv_mem hx)⟩ ∈
      Subgroup.normalizer (Ys : Set (MulAut (IntMod V hV))) := by
    have e : convI hV ⟨x⁻¹, E.hXN (X.inv_mem hx)⟩ = (convI hV ⟨x, E.hXN hx⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [e]
    exact Subgroup.inv_mem _ hxn
  intro z hz
  simpa using key x⁻¹ (X.inv_mem hx) hxinv z hz

theorem autI_baum_le_autI_inf_preI {Ys : Subgroup (MulAut (IntMod V hV))} (hYs : Ys ≤ autI hV L)
    (hS : autI hV (baum R) ≤ Ys) :
    autI hV (baum R) ≤ autI hV (R ⊓ preI hV L E.hLN Ys) := by
  intro φ hφ
  obtain ⟨⟨s, hsN⟩, hsS, rfl⟩ := (mem_autI hV).1 hφ
  have hsR : s ∈ R := E.baum_le_R hsS
  have hsX : s ∈ X := E.R_le_X hsR
  have hsYs : convI hV ⟨s, hsN⟩ ∈ Ys := hS hφ
  obtain ⟨⟨l, hlN⟩, hlL, hle⟩ := (mem_autI hV).1 (hYs hsYs)
  have hC : s * l⁻¹ ∈ X ⊓ Subgroup.centralizer (V : Set G) :=
    ⟨X.mul_mem hsX (X.inv_mem (E.hLX hlL)),
      mul_inv_mem_centralizer (hV := hV) hsN hlN hle.symm⟩
  have hmem : s * l⁻¹ ∈ ((L ⊔ pCoreOf 2 X : Subgroup G) : Set G) := E.C_le_sup hC
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L (pCoreOf 2 X)
    ((pCoreOf_le 2 X).trans E.normal)] at hmem
  obtain ⟨l₂, hl₂, q, hq, hlq⟩ := hmem
  have hlq' : l₂ * q = s * l⁻¹ := hlq
  have hq'Q : l⁻¹ * q * l ∈ pCoreOf 2 X := by
    have := (Subgroup.mem_normalizer_iff.1
      (le_normalizer_pCoreOf 2 X (X.inv_mem (E.hLX hlL))) q).1 hq
    simpa using this
  have hlam : l₂ * l = s * (l⁻¹ * q * l)⁻¹ := by
    have : s = (l₂ * q) * l := by rw [hlq']; group
    calc l₂ * l = (l₂ * q) * l * (l⁻¹ * q * l)⁻¹ := by group
      _ = s * (l⁻¹ * q * l)⁻¹ := by rw [← this]
  have hq'C : l⁻¹ * q * l ∈ Subgroup.centralizer (V : Set G) :=
    (pCoreOf_le_centralizer E.red) hq'Q
  have hlamL : l₂ * l ∈ L := L.mul_mem hl₂ hlL
  have hlamR : l₂ * l ∈ R := by
    rw [hlam]
    exact R.mul_mem hsR (R.inv_mem (E.QR hq'Q))
  have hconv : convI hV ⟨l₂ * l, E.hLN hlamL⟩ = convI hV ⟨s, hsN⟩ := by
    refine convI_eq_of_mul_inv_mem (hV := hV) (E.hLN hlamL) hsN ?_
    rw [hlam]
    have : s * (l⁻¹ * q * l)⁻¹ * s⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
      conj_mem_centralizer_of_le E.hXN hsX (Subgroup.inv_mem _ hq'C)
    simpa [mul_assoc] using this
  have hlamY : l₂ * l ∈ preI hV L E.hLN Ys :=
    (mem_preI hV).2 ⟨hlamL, by rw [convHom_apply, hconv]; exact hsYs⟩
  rw [← hconv]
  exact convI_mem_autI hV (Subgroup.mem_inf.2 ⟨hlamR, hlamY⟩) _

theorem isSylowTwoOf_inf_preI {Ys : Subgroup (MulAut (IntMod V hV))} (hYs : Ys ≤ autI hV L)
    (hsyl : IsSylowTwoOf (autI hV (baum R)) Ys) :
    IsSylowTwoOf (R ⊓ preI hV L E.hLN Ys) (preI hV L E.hLN Ys) := by
  set Y₁ := preI hV L E.hLN Ys with hY₁
  set P := R ⊓ Y₁ with hP
  set K₀ := L ⊓ Subgroup.centralizer (V : Set G) with hK₀
  have hPY₁ : P ≤ Y₁ := inf_le_right
  have hPX : P ≤ X := inf_le_left.trans E.R_le_X
  have hSP := E.autI_baum_le_autI_inf_preI hYs hsyl.1
  have hautP : autI hV P ≤ Ys := (autI_mono hV hPY₁).trans (autI_preI hV hYs).le
  have hsylP : IsSylowTwoOf (autI hV P) Ys :=
    ⟨hautP, isPGroup_autI (E.R_pGroup.to_le inf_le_left), fun hd =>
      hsyl.2.2 (hd.trans (Subgroup.relIndex_dvd_of_le_left Ys hSP))⟩
  have hK₀C : K₀ ≤ X ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf (inf_le_left.trans E.hLX) inf_le_right
  have hCK₀ : X ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (K₀ : Set G) :=
    fun c hc => by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨hxL, hxC⟩
        exact ⟨(Subgroup.mem_normalizer_iff.1 (E.normal hc.1) x).1 hxL,
          conj_mem_centralizer_of_le E.hXN hc.1 hxC⟩
      · rintro ⟨hxL, hxC⟩
        refine ⟨(Subgroup.mem_normalizer_iff.1 (E.normal hc.1) x).2 hxL, ?_⟩
        have := conj_mem_centralizer_of_le E.hXN (X.inv_mem hc.1) hxC
        simpa [mul_assoc] using this
  have hQ₀ : IsSylowTwoOf (pCoreOf 2 X ⊓ K₀) K₀ := B6.isSylowTwoOf_inf_normal E.Csyl hK₀C hCK₀
  have hQ₀eq : pCoreOf 2 X ⊓ K₀ = P ⊓ Subgroup.centralizer (V : Set G) := by
    have hQe : pCoreOf 2 X = R ⊓ Subgroup.centralizer (V : Set G) := E.QC
    ext x
    constructor
    · intro hx
      exact ⟨⟨E.QR hx.1, inf_centralizer_le_preI hV hx.2⟩, hx.2.2⟩
    · intro hx
      exact ⟨by rw [hQe]; exact ⟨hx.1.1, hx.2⟩, ⟨preI_le hV hx.1.2, hx.2⟩⟩
  rw [hQ₀eq] at hQ₀
  have h1 := Subgroup.relIndex_mul_card P Y₁
  rw [inf_eq_left.2 hPY₁] at h1
  have h2 := card_autI_mul_card_inf hV (hPX.trans E.hXN)
  have h3 := Subgroup.relIndex_mul_card (autI hV P) Ys
  rw [inf_eq_left.2 hautP] at h3
  have h4 := Subgroup.relIndex_mul_card (P ⊓ Subgroup.centralizer (V : Set G)) K₀
  rw [inf_eq_left.2 (hQ₀.1)] at h4
  have h5 := card_preI (hA := E.hLN) hV hYs
  have hrab : P.relIndex Y₁ = (autI hV P).relIndex Ys *
      (P ⊓ Subgroup.centralizer (V : Set G)).relIndex K₀ := by
    have hpos : 0 < Nat.card ↥(autI hV P) * Nat.card ↥(P ⊓ Subgroup.centralizer (V : Set G)) :=
      Nat.mul_pos Nat.card_pos Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc P.relIndex Y₁ * (Nat.card ↥(autI hV P) *
            Nat.card ↥(P ⊓ Subgroup.centralizer (V : Set G)))
        = P.relIndex Y₁ * Nat.card ↥P := by rw [h2]
      _ = Nat.card ↥Y₁ := h1
      _ = Nat.card ↥Ys * Nat.card ↥K₀ := h5
      _ = ((autI hV P).relIndex Ys * Nat.card ↥(autI hV P)) *
          ((P ⊓ Subgroup.centralizer (V : Set G)).relIndex K₀ *
            Nat.card ↥(P ⊓ Subgroup.centralizer (V : Set G))) := by rw [h3, h4]
      _ = ((autI hV P).relIndex Ys * (P ⊓ Subgroup.centralizer (V : Set G)).relIndex K₀) *
          (Nat.card ↥(autI hV P) * Nat.card ↥(P ⊓ Subgroup.centralizer (V : Set G))) := by ring
  refine ⟨hPY₁, E.R_pGroup.to_le inf_le_left, fun hd => ?_⟩
  change 2 ∣ P.relIndex Y₁ at hd
  rw [hrab] at hd
  rcases Nat.prime_two.dvd_mul.1 hd with h | h
  · exact hsylP.2.2 h
  · exact hQ₀.2.2 h

theorem mem_omegaOneCenter_baum {v : G} (hv : v ∈ V)
    (hvJ : ∀ j ∈ thompsonJ R, j * v = v * j) : v ∈ quasithinOmegaOneCenter (baum R) := by
  have hvR : v ∈ R := (le_pCoreOf_of_reduced E.red).trans E.QR hv
  have h1 : v ∈ omegaOneOf (R ⊓ Subgroup.centralizer (thompsonJ R : Set G)) :=
    Subgroup.subset_closure ⟨⟨hvR, Subgroup.mem_centralizer_iff.2 hvJ⟩, E.red.2.2.1.2 v hv⟩
  rw [(omegaOne_centralizer_thompsonJ R).1] at h1
  have h2 : omegaOneCenterOf (thompsonJ R) ≤ quasithinOmegaOneCenter (baum R) := by
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    have hgΩ : g ∈ omegaOneCenterOf (thompsonJ R) := Subgroup.subset_closure hg
    refine Subgroup.subset_closure ⟨⟨B6.thompsonJ_le_baum R hg.1.1,
      Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩, hg.2⟩
    exact (Subgroup.mem_centralizer_iff.1 hs.2 g hgΩ).symm
  exact h2 h1

end EntryPlus

end CFSG.Quasithin.C124
