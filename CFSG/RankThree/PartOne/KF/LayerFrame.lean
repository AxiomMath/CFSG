module

public import CFSG.RankThree.PartOne.S12K.FixedLayer
public import CFSG.RankThree.PartOne.S11d.FiveClaimAux
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import CFSG.RankThree.PartOne.KF.LayerModelRow

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.Torsion37

variable {G : Type} [Group G]

structure LayerCore (p : ℕ) (A L : Subgroup G) (b : G) (K : Subgroup G) : Prop where
  b_mem : b ∈ A ∧ b ∈ L ∧ b ≠ 1
  K_eq : K = kLayer L b
  K_qs : CFSG.IsQuasisimple K
  K_center : ¬ p ∣ Nat.card (Subgroup.center K)
  A_K : Nat.card ↥(A ⊓ K) = p
  two : ∃ S : Subgroup G, S ≤ K ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
    A ≤ Subgroup.normalizer (S : Set G) ∧ S = ⁅S, A⁆

namespace LayerCore

variable {p : ℕ} {A L K : Subgroup G} {b : G}

theorem K_le_inf (hd : LayerCore p A L b K) : K ≤ L ⊓ Subgroup.centralizer ({b} : Set G) := by
  rw [hd.K_eq]
  exact Subgroup.map_subtype_le _

theorem K_le_L (hd : LayerCore p A L b K) : K ≤ L := hd.K_le_inf.trans inf_le_left

theorem K_le_centralizer (hd : LayerCore p A L b K) : K ≤ Subgroup.centralizer ({b} : Set G) :=
  hd.K_le_inf.trans inf_le_right

end LayerCore

section Frame

variable [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem Fus12Ctx.L_le_centralizer (ctx : Fus12Ctx G p A c L E) :
    L ≤ Subgroup.centralizer ({c} : Set G) := by
  obtain ⟨L', -, hL'⟩ := ctx.hyp.L_mem.2
  rw [← hL']
  exact Subgroup.map_subtype_le _

theorem Fus12Ctx.not_rowModel_eleven (ctx : Fus12Ctx G p A c L E) : ¬ RowModel p L 11 := by
  intro hmodel
  have hZ := ctx.ten.2.2
  have h1 := hmodel.1
  have h2 := hmodel.2.1
  exact hZ ⟨1, by omega⟩

theorem LayerCore.C_A {K : Subgroup G} {b : G} (ctx : Fus12Ctx G p A c L E)
    (hd : LayerCore p A L b K) :
    A ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers b ⊔ Subgroup.zpowers c := by
  classical
  have h := ctx.hyp
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hAel := h.A_elem
  have hAcard := h.A_card
  have hcA := h.c_mem
  obtain ⟨hbA, hbL, hb1⟩ := hd.b_mem
  have hcL : c ∉ L := ctx.c_not_mem
  have hKc : K ≤ Subgroup.centralizer ({c} : Set G) := hd.K_le_L.trans ctx.L_le_centralizer
  have hKb := hd.K_le_centralizer
  have hbp : b ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) b hbA
  have hcp : c ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) c hcA
  have hbord : orderOf b = p := orderOf_eq_prime hbp hb1
  have hcord : orderOf c = p := orderOf_eq_prime hcp h.c_ne_one
  have hbc : b * c = c * b := congrArg Subtype.val (hAel.is_comm.comm ⟨b, hbA⟩ ⟨c, hcA⟩)
  have hbC : b ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun y hy => Subgroup.mem_centralizer_singleton_iff.1 (hKb hy)
  have hcC : c ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun y hy => Subgroup.mem_centralizer_singleton_iff.1 (hKc hy)
  have hBle : Subgroup.zpowers b ⊔ Subgroup.zpowers c ≤ A ⊓ Subgroup.centralizer (K : Set G) :=
    sup_le (le_inf (Subgroup.zpowers_le.2 hbA) (Subgroup.zpowers_le.2 hbC))
      (le_inf (Subgroup.zpowers_le.2 hcA) (Subgroup.zpowers_le.2 hcC))
  have hdisjbc : Disjoint (Subgroup.zpowers b) (Subgroup.zpowers c) := by
    rw [Subgroup.disjoint_def]
    intro x hxb hxc
    by_contra hx1
    have hzx : Subgroup.zpowers x = Subgroup.zpowers c :=
      zpowers_eq_of_mem_of_ne_one hp hcord hxc hx1
    have hcx : c ∈ Subgroup.zpowers x := hzx ▸ Subgroup.mem_zpowers c
    have hxL : x ∈ L := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxb
      exact Subgroup.zpow_mem _ hbL k
    exact hcL (Subgroup.zpowers_le.2 hxL hcx)
  have hBcard : Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers c) = p ^ 2 := by
    rw [card_sup_of_commute_disjoint (fun x hx y hy => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        exact ((Commute.zpow_zpow (show Commute b c from hbc) i j)).eq) hdisjbc,
      Nat.card_zpowers, Nat.card_zpowers, hbord, hcord]
    ring
  have hDK : Disjoint (A ⊓ Subgroup.centralizer (K : Set G)) (A ⊓ K) := by
    rw [Subgroup.disjoint_def]
    rintro x ⟨hxA, hxC⟩ ⟨-, hxK⟩
    by_contra hx1
    have hxcen : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1 hxC y y.2
    have hxp : x ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) x hxA
    have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
    have hdvd : orderOf (⟨⟨x, hxK⟩, hxcen⟩ : ↥(Subgroup.center ↥K)) ∣
        Nat.card ↥(Subgroup.center ↥K) := orderOf_dvd_natCard _
    have h1 : orderOf (⟨⟨x, hxK⟩, hxcen⟩ : ↥(Subgroup.center ↥K)) = p := by
      rw [← hxord, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe (⟨x, hxK⟩ : ↥K)]
    rw [h1] at hdvd
    exact hd.K_center hdvd
  have hDcard : Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set G)) ≤ p ^ 2 := by
    have hcomm : ∀ x ∈ A ⊓ Subgroup.centralizer (K : Set G), ∀ y ∈ A ⊓ K, x * y = y * x :=
      fun x hx y hy =>
        congrArg Subtype.val (hAel.is_comm.comm ⟨x, hx.1⟩ ⟨y, hy.1⟩)
    have hcard := card_sup_of_commute_disjoint hcomm hDK
    have hle : (A ⊓ Subgroup.centralizer (K : Set G)) ⊔ (A ⊓ K) ≤ A :=
      sup_le inf_le_left inf_le_left
    have h3 := Subgroup.card_le_of_le hle
    rw [hcard, hd.A_K, hAcard] at h3
    have hp0 : 0 < p := hp.pos
    have : Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set G)) * p ≤ p ^ 2 * p := by
      calc _ ≤ p ^ 3 := h3
        _ = p ^ 2 * p := by ring
    exact Nat.le_of_mul_le_mul_right this hp0
  exact (Subgroup.eq_of_le_of_card_ge hBle (by rw [hBcard]; exact hDcard)).symm

theorem LayerCore.exists_I (hS : SchreierFor InCatalog) {K : Subgroup G} {b : G}
    (ctx : Fus12Ctx G p A c L E) (hd : LayerCore p A L b K) :
    ∃ I ∈ thetaComponentsAt p b, K ≤ I := by
  have h := ctx.hyp
  obtain ⟨hbA, hbL, hb1⟩ := hd.b_mem
  have hLmem : L ∈ thetaComponentsAt p c := h.L_mem.2
  have hLsn := isSubnormal_of_mem_thetaComponentsAt hLmem
  have hsn1 := S12K.isSubnormal_kLayer_centralizer (b := b) hLsn
  rw [← hd.K_eq] at hsn1
  have hsn : (K.subgroupOf (Subgroup.centralizer ({c} : Set G) ⊓
      Subgroup.centralizer ({b} : Set G))).IsSubnormal := by
    rw [inf_comm]
    exact hsn1
  exact exists_thetaComponent_ge_of_subnormal hS h.setup h.c_mem h.c_ne_one hbA hb1 hd.K_qs
    (hd.K_le_L.trans ctx.L_le_centralizer) hd.K_le_centralizer hsn

theorem Layer1212.of_core {K I : Subgroup G} {b : G} (ctx : Fus12Ctx G p A c L E)
    (hd : LayerCore p A L b K) (hmodel : LayerModel p L K 1) (hI : I ∈ thetaComponentsAt p b)
    (hKI : K ≤ I) : Layer1212 p A c L E b K I :=
  { b_mem := hd.b_mem
    K_eq := hd.K_eq
    K_qs := hd.K_qs
    K_center := hd.K_center
    K_model := hmodel
    C_A := hd.C_A ctx
    A_K := hd.A_K
    two := hd.two
    I_mem := hI
    K_le := hKI }

end Frame

@[expose] def KF1212LayerRow (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → RowModel p L r → (r ≤ 8 → E = A) → (9 ≤ r → Nat.card E = p ^ 4) →
      ∃ (b : G) (K : Subgroup G), LayerCore p A L b K ∧ RowKClause p L K r

theorem kf1212Layer_of_rows (hS : SchreierFor InCatalog) (hdist : RowModelsDistinct)
    (hrow : ∀ r : ℕ, 1 ≤ r → r ≤ 12 → r ≠ 11 → KF1212LayerRow r) : KF1212Layer := by
  intro G _ _ p A c L E ctx
  obtain ⟨r, hr1, hr12, hmodel, -, hEA, h4⟩ := ctx.facts.three.2
  have hr11 : r ≠ 11 := fun h11 => ctx.not_rowModel_eleven (h11 ▸ hmodel)
  obtain ⟨b, K, hd, hc⟩ := hrow r hr1 hr12 hr11 G p A c L E ctx hmodel hEA h4
  obtain ⟨I, hI, hKI⟩ := hd.exists_I hS ctx
  have hp := ctx.hyp.prime
  have hp2 : p ≠ 2 := by
    have := ctx.hyp.three_lt
    omega
  exact ⟨b, K, I, Layer1212.of_core ctx hd
    (layerModel_of_rowK hdist hp hp2 hr1 hr12 hr11 hmodel hc) hI hKI⟩

end CFSG.RankThree.PartOne
