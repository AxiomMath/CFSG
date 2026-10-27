module

public import CFSG.Milestones.ASVolI.C135.NB
public import CFSG.Milestones.ASVolI.C135.Cent
public import CFSG.Milestones.ASVolI.C135.Coords

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open CFSG.ASVolI.ChC
open CFSG.Quasithin.H13.Ch4 (le_normalizer_c134Q c134Q_le mem_normalizer_centralizer_of_mem)
open CFSG.Quasithin.H13.Ch4.C135 (cnj coe_cnj slNat slNat_surjective dualHom coe_dualHom
  dualHom_dualHom moduleAct_true_eq le_normalizer_centerOf mix mix_apply commutator_mem_Q
  commute_of_mem_pCoreOf)
open scoped Matrix commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure burnsideC135_H1 (X R L : Subgroup G) {F : Type} [Field F] [Fintype F]
    (α : ↥L →* ↥(StatedSL 3 F))
    (β : ↥(c134Q X L) →* Multiplicative (Fin 2 → Fin 3 → F))
    (βU : ↥(centerOf (c134Q X L)) →* Multiplicative (Fin 3 → F)) : Prop where
  card : Fintype.card F = 2
  ms : IsMSPair X R
  comp : L ∈ cComp X
  prod : (X : Set G) = (L : Set G) * (R : Set G)
  normL : X ≤ Subgroup.normalizer (L : Set G)
  surj : IsModO2Surj L α
  cent : X ⊓ Subgroup.centralizer (L : Set G) = ⊥
  nat : IsSumOfNaturalModulesVia L (centerOf (c134Q X L)) ⊥ α false 1
  βs : Function.Surjective β
  βk : β.ker = (centerOf (c134Q X L)).subgroupOf (c134Q X L)
  βeq : ∀ (a : ↥L) (u v : ↥(c134Q X L)), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
    Multiplicative.toAdd (β v) i =
      (moduleAct true (α a : GL (Fin 3) F)).mulVec (Multiplicative.toAdd (β u) i)
  dsg : burnsideC135_DSG (c134Q X L) L (burnsideC135_Wc β 1) (burnsideC135_Wc β 0) (slNat α) βU
    (burnsideC135_βc β 1) (burnsideC135_βc β 0)
  normW : X ≤ Subgroup.normalizer (burnsideC135_Wc β 1 : Set G)

namespace burnsideC135_H1

variable {X R L : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {α : ↥L →* ↥(StatedSL 3 F)} {β : ↥(c134Q X L) →* Multiplicative (Fin 2 → Fin 3 → F)}
  {βU : ↥(centerOf (c134Q X L)) →* Multiplicative (Fin 3 → F)}
  (H : burnsideC135_H1 X R L α β βU)
include H

theorem le : L ≤ X := le_of_mem_cComp H.comp

theorem normQ : X ≤ Subgroup.normalizer (c134Q X L : Set G) := le_normalizer_c134Q H.normL

theorem normU : X ≤ Subgroup.normalizer (centerOf (c134Q X L) : Set G) :=
  le_normalizer_centerOf H.normQ

theorem Q_le : c134Q X L ≤ pCoreOf 2 X :=
  (MS93.commutator_le_pCoreOf H.le H.normL).trans
    (MS93.pCoreOf_le_pCoreOf_of_le_normalizer H.le H.normL)

theorem dual : IsSumOfNaturalModulesVia L (c134Q X L) (centerOf (c134Q X L)) α true 2 :=
  ⟨H.le.trans H.normQ, inf_le_left, β, H.βs, H.βk, H.βeq⟩

theorem comm : ∀ x ∈ c134Q X L, ∀ y ∈ c134Q X L, x * y * x⁻¹ * y⁻¹ ∈ centerOf (c134Q X L) :=
  fun _ hx _ hy => burnsideC135_comm_mem_U H.dual hx hy

theorem T_comm_U {t u : G} (ht : t ∈ pCoreOf 2 X) (hu : u ∈ centerOf (c134Q X L)) :
    t * u = u * t :=
  commute_of_mem_pCoreOf H.surj H.le H.normL H.nat ht hu

theorem centralizer_U_le :
    X ⊓ Subgroup.centralizer (centerOf (c134Q X L) : Set G) ≤ pCoreOf 2 X :=
  burnsideC135_centralizer_U_le' H.ms H.prod H.surj H.le H.normL H.nat

theorem eq_zero_or_one (c : F) : c = 0 ∨ c = 1 := by
  by_contra hc
  push Not at hc
  have h3 : 2 < Fintype.card F :=
    Fintype.two_lt_card_iff.mpr ⟨0, 1, c, zero_ne_one, hc.1.symm, hc.2.symm⟩
  have := H.card
  omega

theorem exists_coords (x y : Fin 3 → F) :
    ∃ q : ↥(c134Q X L), Multiplicative.toAdd (β q) 0 = x ∧ Multiplicative.toAdd (β q) 1 = y := by
  obtain ⟨q, hq⟩ := H.βs (Multiplicative.ofAdd ![x, y])
  exact ⟨q, by rw [hq]; rfl, by rw [hq]; rfl⟩

theorem mem_U_of_coords (q : ↥(c134Q X L)) (h0 : Multiplicative.toAdd (β q) 0 = 0)
    (h1 : Multiplicative.toAdd (β q) 1 = 0) : (q : G) ∈ centerOf (c134Q X L) := by
  have h2 : q ∈ β.ker := by
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    funext i
    rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) i with rfl | rfl
    · exact h0
    · exact h1
  rw [H.βk, Subgroup.mem_subgroupOf] at h2
  exact h2

theorem shear {t : G} (ht : t ∈ pCoreOf 2 X) :
    ∃ μ : F, ∀ (q q' : ↥(c134Q X L)), (q' : G) = t * q * t⁻¹ →
      Multiplicative.toAdd (β q') 0 =
          Multiplicative.toAdd (β q) 0 + μ • Multiplicative.toAdd (β q) 1 ∧
        Multiplicative.toAdd (β q') 1 = Multiplicative.toAdd (β q) 1 := by
  classical
  obtain ⟨c, hc⟩ := burnsideC135_exists_mix H.surj H.le H.normL H.βs H.βk H.βeq ht
  have htX : t ∈ X := pCoreOf_le 2 X ht
  have htQ : t ∈ Subgroup.normalizer (c134Q X L : Set G) := H.normQ htX
  have htW : t ∈ Subgroup.normalizer (burnsideC135_Wc β 1 : Set G) := H.normW htX
  have htU : t ∈ Subgroup.normalizer (centerOf (c134Q X L) : Set G) := H.normU htX
  have e1 : (Pi.single 0 1 : Fin 3 → F) ≠ 0 := fun h => by simpa using congrFun h 0
  have hmix : ∀ (v : Fin 2 → Fin 3 → F) (i : Fin 2), mix c v i = c i 0 • v 0 + c i 1 • v 1 := by
    intro v i
    rw [mix_apply, Fin.sum_univ_two]
  obtain ⟨q₀, hq₀0, hq₀1⟩ := H.exists_coords (Pi.single 0 1) 0
  have hq₀W : (q₀ : G) ∈ burnsideC135_Wc β 1 := burnsideC135_mem_Wc.mpr ⟨q₀.2, hq₀1⟩
  set q₀' : ↥(c134Q X L) := cnj htQ q₀ with hq₀'
  have hc₀ := hc q₀ q₀' rfl
  have hq₀'W : (q₀' : G) ∈ burnsideC135_Wc β 1 :=
    (Subgroup.mem_normalizer_iff.mp htW _).mp hq₀W
  obtain ⟨hh₀, hq₀'1⟩ := burnsideC135_mem_Wc.mp hq₀'W
  have hc10 : c 1 0 = 0 := by
    have h := congrFun hc₀ 1
    rw [hmix, hq₀0, hq₀1, smul_zero, add_zero] at h
    have h' : c 1 0 • (Pi.single 0 1 : Fin 3 → F) = 0 := by rw [← h]; exact hq₀'1
    exact (smul_eq_zero.mp h').resolve_right e1
  have hc00 : c 0 0 = 1 := by
    rcases H.eq_zero_or_one (c 0 0) with h0 | h0
    · exfalso
      have h := congrFun hc₀ 0
      rw [hmix, hq₀0, hq₀1, h0, zero_smul, smul_zero, add_zero] at h
      have hU : (q₀' : G) ∈ centerOf (c134Q X L) := H.mem_U_of_coords q₀' h hq₀'1
      have hU' : (q₀ : G) ∈ centerOf (c134Q X L) := by
        have h2 := (Subgroup.mem_normalizer_iff.mp htU (q₀ : G)).mpr hU
        exact h2
      have h3 : q₀ ∈ β.ker := by
        rw [H.βk, Subgroup.mem_subgroupOf]
        exact hU'
      rw [MonoidHom.mem_ker] at h3
      have h4 : Multiplicative.toAdd (β q₀) 0 = 0 := by rw [h3]; rfl
      rw [hq₀0] at h4
      exact e1 h4
    · exact h0
  obtain ⟨q₁, hq₁0, hq₁1⟩ := H.exists_coords 0 (Pi.single 0 1)
  have hc11 : c 1 1 = 1 := by
    rcases H.eq_zero_or_one (c 1 1) with h0 | h0
    · exfalso
      have h := congrFun (hc q₁ (cnj htQ q₁) rfl) 1
      rw [hmix, hq₁0, hq₁1, h0, zero_smul, smul_zero, add_zero] at h
      have hW : ((cnj htQ q₁ : ↥(c134Q X L)) : G) ∈ burnsideC135_Wc β 1 :=
        burnsideC135_mem_Wc.mpr ⟨(cnj htQ q₁).2, h⟩
      have hW' : (q₁ : G) ∈ burnsideC135_Wc β 1 :=
        (Subgroup.mem_normalizer_iff.mp htW (q₁ : G)).mpr hW
      obtain ⟨hh₁, h1⟩ := burnsideC135_mem_Wc.mp hW'
      have h1' : Multiplicative.toAdd (β q₁) 1 = 0 := h1
      rw [hq₁1] at h1'
      exact e1 h1'
    · exact h0
  refine ⟨c 0 1, fun q q' hq' => ⟨?_, ?_⟩⟩
  · rw [hc q q' hq', hmix, hc00, one_smul]
  · rw [hc q q' hq', hmix, hc10, hc11, zero_smul, zero_add, one_smul]

theorem comm_W₁_mem_U {t w : G} (ht : t ∈ pCoreOf 2 X) (hw : w ∈ burnsideC135_Wc β 1) :
    t * w * t⁻¹ * w⁻¹ ∈ centerOf (c134Q X L) := by
  obtain ⟨μ, hμ⟩ := H.shear ht
  obtain ⟨hwQ, hw1⟩ := burnsideC135_mem_Wc.mp hw
  have htQ : t ∈ Subgroup.normalizer (c134Q X L : Set G) := H.normQ (pCoreOf_le 2 X ht)
  have hmem : t * w * t⁻¹ ∈ c134Q X L := (Subgroup.mem_normalizer_iff.mp htQ w).mp hwQ
  obtain ⟨h0, h1⟩ := hμ ⟨w, hwQ⟩ ⟨_, hmem⟩ rfl
  have h1' : Multiplicative.toAdd (β ⟨w, hwQ⟩) 1 = 0 := hw1
  rw [h1', smul_zero, add_zero] at h0
  rw [h1'] at h1
  have h2 : (⟨w, hwQ⟩ : ↥(c134Q X L))⁻¹ * ⟨_, hmem⟩ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    apply Multiplicative.toAdd.injective
    funext i
    rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) i with rfl | rfl
    · exact h0.symm
    · exact h1'.trans h1.symm
  rw [H.βk, Subgroup.mem_subgroupOf] at h2
  have h3 : w⁻¹ * (t * w * t⁻¹) ∈ centerOf (c134Q X L) := h2
  have e : t * w * t⁻¹ * w⁻¹ = w * (w⁻¹ * (t * w * t⁻¹)) * w⁻¹ := by group
  rw [e]
  have hwN : w ∈ Subgroup.normalizer (centerOf (c134Q X L) : Set G) :=
    le_normalizer_centerOf (fun x hx => Subgroup.le_normalizer hx) hwQ
  exact (Subgroup.mem_normalizer_iff.mp hwN _).mp h3

end burnsideC135_H1

section Coords

variable {X L : Subgroup G} {F : Type} [Field F]
  {β : ↥(c134Q X L) →* Multiplicative (Fin 2 → Fin 3 → F)}
  {βU : ↥(centerOf (c134Q X L)) →* Multiplicative (Fin 3 → F)}

@[expose] noncomputable def burnsideC135_uc
    (βU : ↥(centerOf (c134Q X L)) →* Multiplicative (Fin 3 → F)) (g : G) : Fin 3 → F :=
  haveI := Classical.propDecidable (g ∈ centerOf (c134Q X L))
  if h : g ∈ centerOf (c134Q X L) then Multiplicative.toAdd (βU ⟨g, h⟩) else 0

@[expose] noncomputable def burnsideC135_qc
    (β : ↥(c134Q X L) →* Multiplicative (Fin 2 → Fin 3 → F)) (g : G) : Fin 2 → Fin 3 → F :=
  haveI := Classical.propDecidable (g ∈ c134Q X L)
  if h : g ∈ c134Q X L then Multiplicative.toAdd (β ⟨g, h⟩) else 0

theorem burnsideC135_uc_of_mem {g : G} (h : g ∈ centerOf (c134Q X L)) :
    burnsideC135_uc βU g = Multiplicative.toAdd (βU ⟨g, h⟩) := by
  rw [burnsideC135_uc, dif_pos h]

theorem burnsideC135_qc_of_mem {g : G} (h : g ∈ c134Q X L) :
    burnsideC135_qc β g = Multiplicative.toAdd (β ⟨g, h⟩) := by
  rw [burnsideC135_qc, dif_pos h]

theorem burnsideC135_uc_mul {a b : G} (ha : a ∈ centerOf (c134Q X L)) (hb : b ∈ centerOf (c134Q X L)) :
    burnsideC135_uc βU (a * b) = burnsideC135_uc βU a + burnsideC135_uc βU b := by
  rw [burnsideC135_uc_of_mem ha, burnsideC135_uc_of_mem hb, burnsideC135_uc_of_mem ((centerOf (c134Q X L)).mul_mem ha hb)]
  have e : (⟨a * b, (centerOf (c134Q X L)).mul_mem ha hb⟩ : ↥(centerOf (c134Q X L))) =
      ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
  rw [e, map_mul, toAdd_mul]

theorem burnsideC135_qc_mul {a b : G} (ha : a ∈ c134Q X L) (hb : b ∈ c134Q X L) :
    burnsideC135_qc β (a * b) = burnsideC135_qc β a + burnsideC135_qc β b := by
  rw [burnsideC135_qc_of_mem ha, burnsideC135_qc_of_mem hb, burnsideC135_qc_of_mem ((c134Q X L).mul_mem ha hb)]
  have e : (⟨a * b, (c134Q X L).mul_mem ha hb⟩ : ↥(c134Q X L)) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
  rw [e, map_mul, toAdd_mul]

theorem burnsideC135_uc_inv {a : G} (ha : a ∈ centerOf (c134Q X L)) : burnsideC135_uc βU a⁻¹ = -burnsideC135_uc βU a := by
  have h := burnsideC135_uc_mul (βU := βU) ha ((centerOf (c134Q X L)).inv_mem ha)
  rw [mul_inv_cancel, burnsideC135_uc_of_mem (centerOf (c134Q X L)).one_mem] at h
  have h1 : Multiplicative.toAdd (βU ⟨1, (centerOf (c134Q X L)).one_mem⟩) = 0 := by
    have e : (⟨1, (centerOf (c134Q X L)).one_mem⟩ : ↥(centerOf (c134Q X L))) = 1 := rfl
    rw [e, map_one]
    rfl
  rw [h1] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem burnsideC135_qc_inv {a : G} (ha : a ∈ c134Q X L) : burnsideC135_qc β a⁻¹ = -burnsideC135_qc β a := by
  have h := burnsideC135_qc_mul (β := β) ha ((c134Q X L).inv_mem ha)
  rw [mul_inv_cancel, burnsideC135_qc_of_mem (c134Q X L).one_mem] at h
  have h1 : Multiplicative.toAdd (β ⟨1, (c134Q X L).one_mem⟩) = 0 := by
    have e : (⟨1, (c134Q X L).one_mem⟩ : ↥(c134Q X L)) = 1 := rfl
    rw [e, map_one]
    rfl
  rw [h1] at h
  exact eq_neg_of_add_eq_zero_right h.symm

end Coords

namespace burnsideC135_H1

variable {X R L : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {α : ↥L →* ↥(StatedSL 3 F)} {β : ↥(c134Q X L) →* Multiplicative (Fin 2 → Fin 3 → F)}
  {βU : ↥(centerOf (c134Q X L)) →* Multiplicative (Fin 3 → F)}
  (H : burnsideC135_H1 X R L α β βU)
include H

theorem eq_one_of_uc {a : G} (ha : a ∈ centerOf (c134Q X L)) (h : burnsideC135_uc βU a = 0) : a = 1 := by
  rw [burnsideC135_uc_of_mem ha] at h
  have h1 : βU ⟨a, ha⟩ = βU 1 := by
    rw [map_one]
    exact Multiplicative.toAdd.injective h
  exact congrArg Subtype.val (burnsideC135_βU_injective H.dsg h1)

theorem qc_eq_zero_iff {a : G} (ha : a ∈ c134Q X L) : burnsideC135_qc β a = 0 ↔ a ∈ centerOf (c134Q X L) := by
  rw [burnsideC135_qc_of_mem ha]
  constructor
  · intro h
    have h1 : (⟨a, ha⟩ : ↥(c134Q X L)) ∈ β.ker := by
      rw [MonoidHom.mem_ker]
      exact Multiplicative.toAdd.injective h
    rw [H.βk, Subgroup.mem_subgroupOf] at h1
    exact h1
  · intro h
    have h1 : (⟨a, ha⟩ : ↥(c134Q X L)) ∈ β.ker := by
      rw [H.βk, Subgroup.mem_subgroupOf]
      exact h
    rw [MonoidHom.mem_ker] at h1
    rw [h1]
    rfl

theorem mem_W₁_iff {a : G} : a ∈ burnsideC135_Wc β 1 ↔ a ∈ c134Q X L ∧ burnsideC135_qc β a 1 = 0 := by
  constructor
  · intro h
    obtain ⟨hQ, h1⟩ := burnsideC135_mem_Wc.mp h
    exact ⟨hQ, by rw [burnsideC135_qc_of_mem hQ]; exact h1⟩
  · rintro ⟨hQ, h1⟩
    rw [burnsideC135_qc_of_mem hQ] at h1
    exact burnsideC135_mem_Wc.mpr ⟨hQ, h1⟩

theorem mem_W₂_iff {a : G} : a ∈ burnsideC135_Wc β 0 ↔ a ∈ c134Q X L ∧ burnsideC135_qc β a 0 = 0 := by
  constructor
  · intro h
    obtain ⟨hQ, h1⟩ := burnsideC135_mem_Wc.mp h
    exact ⟨hQ, by rw [burnsideC135_qc_of_mem hQ]; exact h1⟩
  · rintro ⟨hQ, h1⟩
    rw [burnsideC135_qc_of_mem hQ] at h1
    exact burnsideC135_mem_Wc.mpr ⟨hQ, h1⟩

theorem uc_conj {l u : G} (hl : l ∈ L) (hu : u ∈ centerOf (c134Q X L)) :
    burnsideC135_uc βU (l * u * l⁻¹) = ((slNat α ⟨l, hl⟩ : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ burnsideC135_uc βU u := by
  have hmem : l * u * l⁻¹ ∈ centerOf (c134Q X L) :=
    (Subgroup.mem_normalizer_iff.mp (H.normU (H.le hl)) u).mp hu
  rw [burnsideC135_uc_of_mem hmem, burnsideC135_uc_of_mem hu]
  exact H.dsg.natU_act ⟨l, hl⟩ ⟨u, hu⟩ ⟨_, hmem⟩ rfl

theorem qc_conj {l q : G} (hl : l ∈ L) (hq : q ∈ c134Q X L) (i : Fin 2) :
    burnsideC135_qc β (l * q * l⁻¹) i = ((dualHom (slNat α ⟨l, hl⟩) : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ burnsideC135_qc β q i := by
  have hmem : l * q * l⁻¹ ∈ c134Q X L :=
    (Subgroup.mem_normalizer_iff.mp (H.normQ (H.le hl)) q).mp hq
  rw [burnsideC135_qc_of_mem hmem, burnsideC135_qc_of_mem hq, H.βeq ⟨l, hl⟩ ⟨q, hq⟩ ⟨_, hmem⟩ rfl i, moduleAct_true_eq]

theorem uc_comm {w c : G} (hw : w ∈ burnsideC135_Wc β 1) (hc : c ∈ burnsideC135_Wc β 0) :
    burnsideC135_uc βU (w * c * w⁻¹ * c⁻¹) = burnsideC135_qc β w 0 ⨯₃ burnsideC135_qc β c 1 := by
  have hmem := H.comm w (burnsideC135_Wc_le 1 hw) c (burnsideC135_Wc_le 0 hc)
  rw [burnsideC135_uc_of_mem hmem, burnsideC135_comm_cross H.card H.dsg H.comm ⟨w, hw⟩ ⟨c, hc⟩ ⟨_, hmem⟩ rfl,
    burnsideC135_βc_apply, burnsideC135_βc_apply, burnsideC135_qc_of_mem (burnsideC135_Wc_le 1 hw),
    burnsideC135_qc_of_mem (burnsideC135_Wc_le 0 hc)]
  rfl

theorem uc_comm' {c w : G} (hc : c ∈ burnsideC135_Wc β 0) (hw : w ∈ burnsideC135_Wc β 1) :
    burnsideC135_uc βU (c * w * c⁻¹ * w⁻¹) = burnsideC135_qc β c 1 ⨯₃ burnsideC135_qc β w 0 := by
  have hmem := H.comm w (burnsideC135_Wc_le 1 hw) c (burnsideC135_Wc_le 0 hc)
  have e : c * w * c⁻¹ * w⁻¹ = (w * c * w⁻¹ * c⁻¹)⁻¹ := by group
  rw [e, burnsideC135_uc_inv hmem, H.uc_comm hw hc, cross_anticomm]


theorem comm_eq_of_qc {g w w' : G} (hg : g ∈ pCoreOf 2 X) (hw : w ∈ c134Q X L)
    (hw' : w' ∈ c134Q X L) (h : burnsideC135_qc β w = burnsideC135_qc β w') :
    g * w * g⁻¹ * w⁻¹ = g * w' * g⁻¹ * w'⁻¹ := by
  have hu : w⁻¹ * w' ∈ centerOf (c134Q X L) := by
    rw [← H.qc_eq_zero_iff ((c134Q X L).mul_mem ((c134Q X L).inv_mem hw) hw'),
      burnsideC135_qc_mul ((c134Q X L).inv_mem hw) hw', burnsideC135_qc_inv hw, h, neg_add_cancel]
  have hgu := H.T_comm_U hg hu
  have e : w' = w * (w⁻¹ * w') := by group
  rw [e]
  calc g * w * g⁻¹ * w⁻¹ = g * w * ((w⁻¹ * w') * g⁻¹ * (w⁻¹ * w')⁻¹) * w⁻¹ := by
        rw [show (w⁻¹ * w') * g⁻¹ * (w⁻¹ * w')⁻¹ = g⁻¹ by
          rw [show (w⁻¹ * w') * g⁻¹ = g⁻¹ * (w⁻¹ * w') by
            rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, hgu, mul_assoc, mul_inv_cancel, mul_one]]
          group]
    _ = g * (w * (w⁻¹ * w')) * g⁻¹ * (w * (w⁻¹ * w'))⁻¹ := by group

omit H in
theorem comm_mul_left' {g c w : G} (h : g * (c * w * c⁻¹ * w⁻¹) = (c * w * c⁻¹ * w⁻¹) * g) :
    (g * c) * w * (g * c)⁻¹ * w⁻¹ = (c * w * c⁻¹ * w⁻¹) * (g * w * g⁻¹ * w⁻¹) := by
  calc (g * c) * w * (g * c)⁻¹ * w⁻¹ = (g * (c * w * c⁻¹ * w⁻¹)) * g⁻¹ * (g * w * g⁻¹ * w⁻¹) := by
        group
    _ = (c * w * c⁻¹ * w⁻¹) * (g * w * g⁻¹ * w⁻¹) := by rw [h]; group

omit H in
theorem comm_mul_right' {g a b : G} (h : a * (g * b * g⁻¹ * b⁻¹) = (g * b * g⁻¹ * b⁻¹) * a) :
    g * (a * b) * g⁻¹ * (a * b)⁻¹ = (g * a * g⁻¹ * a⁻¹) * (g * b * g⁻¹ * b⁻¹) := by
  calc g * (a * b) * g⁻¹ * (a * b)⁻¹ = (g * a * g⁻¹ * a⁻¹) * (a * (g * b * g⁻¹ * b⁻¹)) * a⁻¹ := by
        group
    _ = (g * a * g⁻¹ * a⁻¹) * (g * b * g⁻¹ * b⁻¹) := by rw [h]; group

theorem U_comm' {u x : G} (hu : u ∈ centerOf (c134Q X L)) (hx : x ∈ c134Q X L) :
    x * u = u * x :=
  Subgroup.mem_centralizer_iff.mp hu.2 x hx

theorem exists_mul_mem_V {t : G} (ht : t ∈ pCoreOf 2 X) :
    ∃ c ∈ burnsideC135_Wc β 0, t * c ∈ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G) := by
  classical
  have hW₁Q : burnsideC135_Wc β 1 ≤ c134Q X L := burnsideC135_Wc_le 1
  have hW₂Q : burnsideC135_Wc β 0 ≤ c134Q X L := burnsideC135_Wc_le 0
  obtain ⟨hsq₁, -⟩ := burnsideC135_W_sq H.dsg
  choose s hs0 hs1 using fun x : Fin 3 → F => H.exists_coords x 0
  have hsQ : ∀ x, ((s x : ↥(c134Q X L)) : G) ∈ c134Q X L := fun x => (s x).2
  have hsc : ∀ x, burnsideC135_qc β (s x) = ![x, 0] := by
    intro x
    rw [burnsideC135_qc_of_mem (hsQ x)]
    funext i
    rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) i with rfl | rfl
    · exact hs0 x
    · exact hs1 x
  have hsW : ∀ x, ((s x : ↥(c134Q X L)) : G) ∈ burnsideC135_Wc β 1 := fun x =>
    H.mem_W₁_iff.mpr ⟨hsQ x, by rw [hsc]; rfl⟩
  have hqcW : ∀ w ∈ burnsideC135_Wc β 1, burnsideC135_qc β w = ![burnsideC135_qc β w 0, 0] := by
    intro w hw
    funext i
    rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) i with rfl | rfl
    · rfl
    · exact (H.mem_W₁_iff.mp hw).2
  let D : (Fin 3 → F) → (Fin 3 → F) := fun x =>
    burnsideC135_uc βU (t * s x * t⁻¹ * ((s x : ↥(c134Q X L)) : G)⁻¹)
  have hDw : ∀ w ∈ burnsideC135_Wc β 1,
      burnsideC135_uc βU (t * w * t⁻¹ * w⁻¹) = D (burnsideC135_qc β w 0) := by
    intro w hw
    show _ = burnsideC135_uc βU (t * s _ * t⁻¹ * ((s _ : ↥(c134Q X L)) : G)⁻¹)
    rw [H.comm_eq_of_qc ht (hW₁Q hw) (hsQ _) (by rw [hsc, hqcW w hw])]
  have hDadd : ∀ x x', D (x + x') = D x + D x' := by
    intro x x'
    have hmul : ((s x : ↥(c134Q X L)) : G) * s x' ∈ burnsideC135_Wc β 1 :=
      (burnsideC135_Wc β 1).mul_mem (hsW x) (hsW x')
    have h1 : burnsideC135_qc β (((s x : ↥(c134Q X L)) : G) * s x') 0 = x + x' := by
      rw [burnsideC135_qc_mul (hsQ x) (hsQ x'), hsc, hsc]
      rfl
    have h2 := hDw _ hmul
    rw [h1] at h2
    rw [← h2, comm_mul_right' (H.U_comm' (H.comm_W₁_mem_U ht (hsW x')) (hsQ x)),
      burnsideC135_uc_mul (H.comm_W₁_mem_U ht (hsW x)) (H.comm_W₁_mem_U ht (hsW x'))]
  have hrel : ∀ γ : Matrix.SpecialLinearGroup (Fin 3) F, ∃ y : Fin 3 → F, ∀ v,
      (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ D ((γ : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v) =
        D v + y ⨯₃ v := by
    intro γ
    obtain ⟨l, hl⟩ := slNat_surjective H.surj.1 γ
    have hcQ : t⁻¹ * l * t * (l : G)⁻¹ ∈ c134Q X L := commutator_mem_Q ht l.2
    set c := t⁻¹ * l * t * (l : G)⁻¹ with hcdef
    obtain ⟨c₂, hc₂0, hc₂1⟩ := H.exists_coords 0 (burnsideC135_qc β c 1)
    have hc₂Q : ((c₂ : ↥(c134Q X L)) : G) ∈ c134Q X L := c₂.2
    have hc₂c : burnsideC135_qc β c₂ = ![0, burnsideC135_qc β c 1] := by
      rw [burnsideC135_qc_of_mem hc₂Q]
      funext i
      rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) i with rfl | rfl
      · exact hc₂0
      · exact hc₂1
    have hc₂W : ((c₂ : ↥(c134Q X L)) : G) ∈ burnsideC135_Wc β 0 :=
      H.mem_W₂_iff.mpr ⟨hc₂Q, by rw [hc₂c]; rfl⟩
    set c₁ := c * ((c₂ : ↥(c134Q X L)) : G)⁻¹ with hc₁def
    have hc₁Q : c₁ ∈ c134Q X L := (c134Q X L).mul_mem hcQ ((c134Q X L).inv_mem hc₂Q)
    have hc₁W : c₁ ∈ burnsideC135_Wc β 1 := by
      refine H.mem_W₁_iff.mpr ⟨hc₁Q, ?_⟩
      rw [burnsideC135_qc_mul hcQ ((c134Q X L).inv_mem hc₂Q), burnsideC135_qc_inv hc₂Q, hc₂c]
      simp
    have hc12 : c = c₁ * c₂ := by rw [hc₁def]; group
    refine ⟨burnsideC135_qc β c 1, fun x => ?_⟩
    have hlinv : ((l : G))⁻¹ ∈ L := L.inv_mem l.2
    have hw'mem : (l : G)⁻¹ * s x * ((l : G)⁻¹)⁻¹ ∈ burnsideC135_Wc β 1 :=
      (Subgroup.mem_normalizer_iff.mp (H.dsg.norm₁ hlinv) _).mp (hsW x)
    have hw'c : burnsideC135_qc β ((l : G)⁻¹ * s x * ((l : G)⁻¹)⁻¹) 0 =
        (γ : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ x := by
      rw [H.qc_conj hlinv (hsQ x) 0, hsc]
      have e : (⟨((l : G))⁻¹, hlinv⟩ : ↥L) = l⁻¹ := rfl
      rw [e, map_inv, hl, coe_dualHom, inv_inv]
      rfl
    have hUcomm := H.comm_W₁_mem_U ht hw'mem
    have h1 := hDw _ hw'mem
    rw [hw'c] at h1
    have hconj := H.uc_conj l.2 hUcomm
    rw [show (⟨(l : G), l.2⟩ : ↥L) = l from rfl, hl] at hconj
    rw [← h1, ← hconj]
    have e2 : (l : G) * (t * ((l : G)⁻¹ * s x * ((l : G)⁻¹)⁻¹) * t⁻¹ *
        ((l : G)⁻¹ * s x * ((l : G)⁻¹)⁻¹)⁻¹) * (l : G)⁻¹ =
        (t * c) * s x * (t * c)⁻¹ * ((s x : ↥(c134Q X L)) : G)⁻¹ := by
      rw [hcdef]; group
    have hcwU : c * s x * c⁻¹ * ((s x : ↥(c134Q X L)) : G)⁻¹ ∈ centerOf (c134Q X L) :=
      H.comm c hcQ _ (hsQ x)
    have hc₂wU : ((c₂ : ↥(c134Q X L)) : G) * s x * ((c₂ : ↥(c134Q X L)) : G)⁻¹ *
        ((s x : ↥(c134Q X L)) : G)⁻¹ ∈ centerOf (c134Q X L) := H.comm _ hc₂Q _ (hsQ x)
    have hslU := (H.comm_W₁_mem_U ht (hsW x))
    have e3 : c * s x * c⁻¹ * ((s x : ↥(c134Q X L)) : G)⁻¹ =
        (c₁ * c₂) * s x * (c₁ * c₂)⁻¹ * ((s x : ↥(c134Q X L)) : G)⁻¹ := by rw [← hc12]
    rw [e2, comm_mul_left' (H.T_comm_U ht hcwU), burnsideC135_uc_mul hcwU hslU, e3,
      comm_mul_left' (H.U_comm' hc₂wU hc₁Q)]
    have hc₁w : c₁ * s x * c₁⁻¹ * ((s x : ↥(c134Q X L)) : G)⁻¹ = 1 := by
      rw [burnsideC135_comm_of_sq hsq₁ hc₁W (hsW x)]; group
    rw [hc₁w, mul_one, H.uc_comm' hc₂W (hsW x), hc₂c, hsc]
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
    rw [add_comm]
  obtain ⟨y₀, hy₀⟩ := burnsideC135_weight H.card D hDadd hrel
  obtain ⟨c₀, hc₀0, hc₀1⟩ := H.exists_coords 0 (-y₀)
  have hc₀Q : ((c₀ : ↥(c134Q X L)) : G) ∈ c134Q X L := c₀.2
  have hc₀W : ((c₀ : ↥(c134Q X L)) : G) ∈ burnsideC135_Wc β 0 :=
    H.mem_W₂_iff.mpr ⟨hc₀Q, by rw [burnsideC135_qc_of_mem hc₀Q]; exact hc₀0⟩
  refine ⟨c₀, hc₀W, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
  have hwQ := hW₁Q hw
  have hcwU := H.comm _ hc₀Q w hwQ
  have htwU := H.comm_W₁_mem_U ht hw
  have h1 : (t * c₀) * w * (t * c₀)⁻¹ * w⁻¹ = 1 := by
    refine H.eq_one_of_uc ?_ ?_
    · rw [comm_mul_left' (H.T_comm_U ht hcwU)]
      exact (centerOf (c134Q X L)).mul_mem hcwU htwU
    · rw [comm_mul_left' (H.T_comm_U ht hcwU), burnsideC135_uc_mul hcwU htwU,
        H.uc_comm' hc₀W hw, hDw w hw, hy₀]
      have h2 : burnsideC135_qc β c₀ 1 = -y₀ := by rw [burnsideC135_qc_of_mem hc₀Q]; exact hc₀1
      rw [h2, LinearMap.map_neg₂, neg_add_cancel]
  calc w * (t * c₀) = ((t * c₀) * w * (t * c₀)⁻¹ * w⁻¹)⁻¹ * ((t * c₀) * w) := by group
    _ = (t * c₀) * w := by rw [h1, inv_one, one_mul]

end burnsideC135_H1

end CFSG.ASVolI

end
