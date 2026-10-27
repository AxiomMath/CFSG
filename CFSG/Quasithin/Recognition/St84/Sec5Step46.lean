module

public import CFSG.Quasithin.Recognition.St84.Sec5Step3
public import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient
import CFSG.Quasithin.Recognition.St84.Gen.Sec6Cover
public import CFSG.Quasithin.EmptyFaithful.S146S3

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s n₀ : ℕ}

namespace Setup

private theorem le_arcStab_of_le_Zt (Y : Setup Γ G) {r₀ : ℕ} {X : Subgroup G}
    (he : Y.ZtExt 0 r₀ r₀) (heven : Even r₀) (h0 : X ≤ Y.Zt 0) (hr : X ≤ Y.Zt (r₀ : ℤ)) :
    X ≤ Y.arcStab (-(r₀ : ℤ)) (-(r₀ : ℤ) + ((3 * r₀ : ℕ) : ℤ)) := by
  obtain ⟨k, hk⟩ := heven
  have hcast : (r₀ : ℤ) = 2 * (k : ℤ) := by
    have h : (r₀ : ℤ) = (k : ℤ) + (k : ℤ) := by exact_mod_cast hk
    linarith
  have hcast3 : ((3 * r₀ : ℕ) : ℤ) = 3 * (r₀ : ℤ) := by push_cast; ring
  intro x hx
  rw [Setup.arcStab, Fan86.mem_fixSet]
  rintro v ⟨i, hi, rfl⟩
  obtain ⟨hil, hiu⟩ := Set.mem_Icc.mp hi
  rw [hcast3] at hiu
  rcases le_total i (r₀ : ℤ) with hle | hge
  · have hxGi : x ∈ Y.Gi (0 + i) := he.1 i (by linarith) hle (h0 hx)
    have h := MulAction.mem_stabilizer_iff.mp hxGi
    simpa using h
  · have h1 : -(r₀ : ℤ) ≤ i - (r₀ : ℤ) := by linarith
    have h2 : i - (r₀ : ℤ) ≤ (r₀ : ℤ) := by linarith
    have htr := he.Zt_two_mul_le_Gi (k : ℤ) (i - (r₀ : ℤ)) h1 h2
    have hZt : Y.Zt (2 * (k : ℤ)) = Y.Zt (r₀ : ℤ) := by rw [hcast]
    rw [hZt] at htr
    have hxGi : x ∈ Y.Gi (2 * (k : ℤ) + (i - (r₀ : ℤ))) := htr (hr hx)
    have h := MulAction.mem_stabilizer_iff.mp hxGi
    have harg : 2 * (k : ℤ) + (i - (r₀ : ℤ)) = i := by linarith
    rwa [harg] at h


private theorem eq_edgeSylow_zero_of_not_le (Y : Setup Γ G) (h : ¬ Y.Z 0 ≤ Y.Q 1) :
    Y.Z 0 ⊔ Y.Q 1 = Y.edgeSylow 0 := by
  have hKZ : Y.K ≤ Subgroup.normalizer (Y.Z 0 : Set G) := Y.K_le_normalizer_Z 0
  simpa using Y.sup_Q_eq_edgeSylow_of_gen 0 (inf_le_left.trans hKZ)
    ((Y.Z_le_Q 0).trans (Y.Q_le_edgeSylow_left 0)) (by simpa using h)


private theorem Z_one_le_Qs_and_Q_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (h3 : Y.Zt 1 = ⊥) : Y.Z 1 ≤ Y.Qs 1 ∧ Y.Z 1 ≤ Y.Q 0 := by
  have hZ1K : Y.Z 1 ≤ Subgroup.centralizer (Y.K : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  have hZ1Q1 : Y.Z 1 ≤ Y.Q 1 := Y.Z_le_Q 1
  have hZ1p : IsPGroup 2 (Y.Z 1) := (pCoreOf_isPGroup' (Y.Gi 1)).to_le hZ1Q1
  have hZ1G0 : Y.Z 1 ≤ Y.Gi 0 := by
    simpa using hZ1Q1.trans ((Y.Q_le_Gi_adj 1).trans inf_le_left)
  have hK : ⁅Y.Z 1, Y.K⁆ = ⊥ := h3
  refine ⟨le_inf hZ1Q1 hZ1K, ?_⟩
  exact le_Q_of_comm_K_eq_bot Y H (j := 0) (by norm_num) hZ1G0 hZ1p hK

private theorem centerOf_L_one_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    centerOf (Y.L 1) = Y.Z 1 ⊓ Subgroup.centralizer (Y.J 1 : Set G) := by
  have hLJ : Y.L 1 = Y.J 1 ⊔ Y.Q 1 := (J_sup_Q_and_inv Y H).1
  have hZ1CQ1 : Y.Z 1 ≤ Subgroup.centralizer (Y.Q 1 : Set G) :=
    (Y.Z_le_center 1).trans inf_le_right
  refine le_antisymm ?_ ?_
  · intro z hz
    refine Subgroup.mem_inf.mpr ⟨(centerOf_L_le_Z (X := Y) H.char 1) hz, ?_⟩
    exact Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr (hLJ.symm ▸ le_sup_left)) hz.2
  · intro z hz
    obtain ⟨hzZ, hzJ⟩ := Subgroup.mem_inf.mp hz
    have hzQ : z ∈ Subgroup.centralizer (Y.Q 1 : Set G) := hZ1CQ1 hzZ
    have hJ : ∀ j ∈ Y.J 1, j * z = z * j := fun j hj =>
      Subgroup.mem_centralizer_iff.mp hzJ j hj
    have hQ : ∀ q ∈ Y.Q 1, q * z = z * q := fun q hq =>
      Subgroup.mem_centralizer_iff.mp hzQ q hq
    have hzL : z ∈ Y.L 1 := by
      rw [hLJ]
      exact Subgroup.mem_sup_right (Y.Z_le_Q 1 hzZ)
    refine Subgroup.mem_inf.mpr ⟨hzL, ?_⟩
    have hLz : Y.L 1 ≤ Subgroup.centralizer ({z} : Set G) := by
      rw [hLJ]
      exact sup_le (fun j hj => Subgroup.mem_centralizer_singleton_iff.mpr (hJ j hj))
        (fun q hq => Subgroup.mem_centralizer_singleton_iff.mpr (hQ q hq))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLz hy)


private theorem Z_one_eq_center_of_small_Qs (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (h3 : Y.Zt 1 = ⊥) (hQ : Nat.card (Y.Qs 1) ≤ 2) : Y.Z 1 = centerOf (Y.L 1) := by
  have hZ1Qs : Y.Z 1 ≤ Y.Qs 1 := (Z_one_le_Qs_and_Q_zero Y H h3).1
  have hnorm := J_one_le_normalizer_Qs_one Y H
  haveI hQfin : Finite ↥(Y.Qs 1) :=
    finite_of_le_stabilizer Y.hyp (H := Y.Qs 1)
      ((inf_le_left : Y.Q 1 ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.Q 1).trans (Y.Q_le_Gi 1))
  have hcent : Y.Qs 1 ≤ Subgroup.centralizer (Y.J 1 : Set G) := by
    obtain h1 | h2 : Nat.card (Y.Qs 1) = 1 ∨ Nat.card (Y.Qs 1) = 2 := by
      have := Nat.card_pos (α := Y.Qs 1)
      omega
    · exact (Subgroup.card_eq_one.mp h1).le.trans bot_le
    · exact Subgroup.le_centralizer_iff.mp
        (hnorm.trans (CFSG.Quasithin.normalizer_eq_centralizer_of_card_eq_two h2).le)
  have hZ1CJ : Y.Z 1 ≤ Subgroup.centralizer (Y.J 1 : Set G) := hZ1Qs.trans hcent
  rw [centerOf_L_one_eq Y H]
  exact le_antisymm (le_inf (le_refl _) hZ1CJ) inf_le_left

private theorem Z_one_eq_center_of_not_le (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (h3 : Y.Zt 1 = ⊥) (h0 : ¬ Y.Z 0 ≤ Y.Q 1) : Y.Z 1 = centerOf (Y.L 1) := by
  have h1 : Y.Z 1 ≤ Y.Q 0 := (Z_one_le_Qs_and_Q_zero Y H h3).2
  have hS : Y.Z 0 ⊔ Y.Q 1 = Y.S := by
    rw [eq_edgeSylow_zero_of_not_le Y h0, Setup.edgeSylow_zero]
  exact Z_eq_center_of_sup Y 1 0 (by norm_num) h1 hS


theorem L_one_le_sup_of_hasB_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hb : Y.HasB 0 1) :
    Y.L 1 ≤ Y.Z 0 ⊔ Y.Z 2 ⊔ Y.Q 1 :=
  Y.L_one_le_sup_of_not_Z_zero_le_Q_one H fun h =>
    hb.2.1 (by simpa using h.trans ((Y.Q_le_Gi_adj 1).trans inf_le_right))

theorem Z_inf_Z_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (h4 : Y.Z 1 = centerOf (Y.L 1)) (hb : Y.HasB 0 1) :
    Y.Z 0 ⊓ Y.Z 2 = Y.Z 1 := by
  have hgen : Y.L 1 ≤ Y.Z 0 ⊔ Y.Z 2 ⊔ Y.Q 1 := L_one_le_sup_of_hasB_one Y H hb
  have hZ1Q0 : Y.Z 1 ≤ Y.Q 0 := by
    rw [h4]
    exact (Y.centerOf_L_le_Q_adj H.char 0).1
  have hSL : Y.S ≤ Y.L 1 := Y.S_le_L_one
  have hZ1S : Y.Z 1 ≤ Subgroup.centralizer (Y.S : Set G) := by
    rw [h4]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_iff.mp hz.2 s (hSL hs)
  have hE0L : Y.edgeSylow 0 ≤ Y.L 1 := by
    have h := le_oTwoPrime_of_isPGroup (Y.isPGroup_edgeSylow 0)
      ((Y.isSylowTwoOf_edgeSylow 0).1.trans inf_le_right)
    simpa [Setup.edgeSylow_zero] using h
  have hZ1Z0 : Y.Z 1 ≤ Y.Z 0 := by
    have hZ1S' : Y.Z 1 ≤ Y.S := hZ1Q0.trans (Y.Q_le_edgeSylow_left 0)
    have hle : Y.Z 1 ≤ centerOf Y.S := le_inf hZ1S' hZ1S
    exact hle.trans (center_S_le_Z Y H 0 (Or.inl rfl)).1
  have hZ1Z2 : Y.Z 1 ≤ Y.Z 2 := by
    obtain ⟨g, hgG1, hg02⟩ := Y.hyp.locTrans (Y.adj 0).symm (Y.adj 1)
    have hZ2 : Y.Z 2 = conjSub g (Y.Z 0) := Setup.Z_smul Y Y hg02
    have hGi1 : conjSub g (Y.Gi 1) = Y.Gi 1 := conjSub_eq_of_mem hgG1
    have hLconj : conjSub g (Y.L 1) = Y.L 1 := by
      rw [show Y.L 1 = oTwoPrime (Y.Gi 1) from rfl, conjSub_oTwoPrime, hGi1]
    have hconjZ1 : conjSub g (Y.Z 1) = Y.Z 1 := by
      rw [h4]
      exact (centerOf_conjSub g (Y.L 1)).symm.trans (by rw [hLconj])
    rw [hZ2, ← hconjZ1]
    exact conjSub_mono g hZ1Z0
  refine le_antisymm ?_ (le_inf hZ1Z0 hZ1Z2)
  intro x hx
  obtain ⟨hx0, hx2⟩ := Subgroup.mem_inf.mp hx
  have hxL : x ∈ Y.L 1 :=
    (((Y.Z_le_Q 0).trans (Y.Q_le_edgeSylow_left 0)).trans hE0L) hx0
  have hxZ0 : Y.Z 0 ≤ Subgroup.centralizer ({x} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Y.Z_commute 0 y hy x hx0)
  have hxZ2 : Y.Z 2 ≤ Subgroup.centralizer ({x} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Y.Z_commute 2 y hy x hx2)
  have hxQ0 : Y.Q 0 ≤ Subgroup.centralizer ({x} : Set G) := by
    intro q hq
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (Y.Z_le_center 0 hx0).2 q hq)
  have hxQ2 : Y.Q 2 ≤ Subgroup.centralizer ({x} : Set G) := by
    intro q hq
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (Y.Z_le_center 2 hx2).2 q hq)
  have hxQ1 : Y.Q 1 ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [Q_eq_sup_inf Y H 1]
    exact sup_le (fun y hy => hxQ0 (Subgroup.mem_inf.mp hy).1)
      (fun y hy => hxQ2 (Subgroup.mem_inf.mp hy).1)
  have hxA : Y.Z 0 ⊔ Y.Z 2 ⊔ Y.Q 1 ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le (sup_le hxZ0 hxZ2) hxQ1
  have hxcentA : x ∈ Subgroup.centralizer
      ((Y.Z 0 ⊔ Y.Z 2 ⊔ Y.Q 1 : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (hxA ha)
  have hxcentL : x ∈ Subgroup.centralizer (Y.L 1 : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hgen) hxcentA
  rw [h4]
  exact Subgroup.mem_inf.mpr ⟨hxL, hxcentL⟩

private theorem centralizer_zpowers_eq_singleton {H : Type*} [Group H] (d : H) :
    Subgroup.centralizer (Subgroup.zpowers d : Set H) = Subgroup.centralizer ({d} : Set H) := by
  ext x
  show (∀ h ∈ (Subgroup.zpowers d : Set H), h * x = x * h) ↔
    (∀ h ∈ ({d} : Set H), h * x = x * h)
  constructor
  · intro h
    simpa using h d (Subgroup.mem_zpowers d)
  · intro h y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (show Commute d x from h d (by simp)).zpow_left n

private theorem map_centralizer_subgroupOf {H : Type*} [Group H] {A B : Subgroup H}
    (hB : B ≤ A) :
    (Subgroup.centralizer (B.subgroupOf A : Set ↥A)).map A.subtype =
      Subgroup.centralizer (B : Set H) ⊓ A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, y.2⟩
    show ∀ b ∈ (B : Set H), b * (y : H) = (y : H) * b
    intro b hb
    have := hy ⟨b, hB hb⟩ (Subgroup.mem_subgroupOf.mpr hb)
    exact congrArg Subtype.val this
  · rintro ⟨hx1, hx2⟩
    refine ⟨⟨x, hx2⟩, ?_, rfl⟩
    show ∀ b ∈ (B.subgroupOf A : Set ↥A), b * (⟨x, hx2⟩ : ↥A) = (⟨x, hx2⟩ : ↥A) * b
    intro b hb
    apply Subtype.ext
    exact hx1 b (Subgroup.mem_subgroupOf.mp hb)

private theorem abelian_fitting_decomp_of_zpowers (Y : Setup Γ G) {X : Subgroup G} {d : G}
    (hdG : d ∈ Y.Gi 1) (hd3 : orderOf d = 3)
    (hXnorm : Subgroup.zpowers d ≤ Subgroup.normalizer (X : Set G))
    (hX : X ≤ Y.Gi 1) (hXp : IsPGroup 2 X)
    (hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    X = (X ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ ⁅X, Subgroup.zpowers d⁆ ∧
      (X ⊓ Subgroup.centralizer ({d} : Set G)) ⊓ ⁅X, Subgroup.zpowers d⁆ = ⊥ := by
  classical
  haveI : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  let M : Subgroup ↥(Y.Gi 1) := X.subgroupOf (Y.Gi 1)
  let S : Subgroup ↥(Y.Gi 1) := (Subgroup.zpowers d).subgroupOf (Y.Gi 1)
  let N : Subgroup ↥(Y.Gi 1) := ⁅M, S⁆
  have hSM : S ≤ Subgroup.normalizer (M : Set ↥(Y.Gi 1)) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hX]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hXnorm hx)
  have hNM : N ≤ M := by
    rw [Subgroup.commutator_le]
    intro m hm s hs
    have hconj : s * m⁻¹ * s⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.mp (hSM hs) m⁻¹).mp (M.inv_mem hm)
    have heq : m * s * m⁻¹ * s⁻¹ = m * (s * m⁻¹ * s⁻¹) := by group
    rw [commutatorElement_def, heq]
    exact M.mul_mem hm hconj
  have hMN : M ≤ Subgroup.normalizer (N : Set ↥(Y.Gi 1)) :=
    Subgroup.normalizer_commutator_ge_left M S
  have hSN : S ≤ Subgroup.normalizer (N : Set ↥(Y.Gi 1)) :=
    Subgroup.normalizer_commutator_ge_right M S
  have hMcomm : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ (⊥ : Subgroup ↥(Y.Gi 1)) := by
    intro x hx y hy
    have hxZ : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    have hyZ : (y : G) ∈ X := Subgroup.mem_subgroupOf.mp hy
    rw [Subgroup.mem_bot]
    refine Subtype.ext ?_
    show (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ = 1
    rw [hXab x hxZ y hyZ]
    group
  haveI hMcomm' : IsMulCommutative M :=
    IsMulCommutative.of_comm (fun x y => by
      have hxZ : (((x : M) : ↥(Y.Gi 1)) : G) ∈ X := Subgroup.mem_subgroupOf.mp x.2
      have hyZ : (((y : M) : ↥(Y.Gi 1)) : G) ∈ X := Subgroup.mem_subgroupOf.mp y.2
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact hXab _ hxZ _ hyZ)
  have hMsolv : Group.IsSolvable M := inferInstance
  have hScard : Nat.card ↥S = 3 := by
    rw [show Nat.card ↥S = Nat.card ↥(Subgroup.zpowers d) from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hdG))]
    rw [Nat.card_zpowers, hd3]
  have hMp : IsPGroup 2 M := by
    haveI : Finite ↥X := finite_of_le_stabilizer Y.hyp (H := X) hX
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hXp
    refine IsPGroup.of_card (n := n) ?_
    rw [show Nat.card ↥M = Nat.card ↥X from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX)]
    exact hn
  have hcop : Nat.Coprime (Nat.card ↥S) (Nat.card ↥M) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hMp
    rw [hScard, hm]
    exact (by norm_num : Nat.Coprime 3 2).pow_right m
  have hfix : ∀ m ∈ M, ∀ s ∈ S, m⁻¹ * (s * m * s⁻¹) ∈ N := by
    intro m hm s hs
    have hcomm : ⁅s, m⁆ ∈ N := by
      have h : ⁅s, m⁆ ∈ ⁅S, M⁆ := Subgroup.commutator_mem_commutator hs hm
      rwa [Subgroup.commutator_comm] at h
    have heq : m⁻¹ * (s * m * s⁻¹) = m⁻¹ * ⁅s, m⁆ * m := by
      rw [commutatorElement_def]; group
    rw [heq]
    have hmN' : m⁻¹ ∈ Subgroup.normalizer (N : Set ↥(Y.Gi 1)) :=
      (Subgroup.normalizer (N : Set ↥(Y.Gi 1))).inv_mem (hMN hm)
    have := (Subgroup.mem_normalizer_iff.mp hmN' ⁅s, m⁆).mp hcomm
    simpa using this
  have hdecomp : ∀ m ∈ M, ∃ c ∈ M ⊓ Subgroup.centralizer (S : Set ↥(Y.Gi 1)),
      ∃ n ∈ N, m = c * n := by
    intro m hm
    exact CFSG.LocalAnalysis.EvenBN.Common.exists_mem_inf_centralizer_mul_of_coprime
      hNM hMN hSM hSN hMsolv hcop hm (hfix m hm)
  have hsupM : M = (M ⊓ Subgroup.centralizer (S : Set ↥(Y.Gi 1))) ⊔ N := by
    refine le_antisymm ?_ (sup_le inf_le_left hNM)
    intro m hm
    obtain ⟨c, hc, n, hn, rfl⟩ := hdecomp m hm
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hn)
  have hdisjM : (M ⊓ Subgroup.centralizer (S : Set ↥(Y.Gi 1))) ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxC, hxN⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxM, hxcent⟩ := Subgroup.mem_inf.mp hxC
    have hx' : x ∈ ⁅S, M⁆ ⊔ (⊥ : Subgroup ↥(Y.Gi 1)) := by
      rw [sup_bot_eq, Subgroup.commutator_comm]
      exact hxN
    have hfixx : ∀ a ∈ S, a * x * a⁻¹ * x⁻¹ ∈ (⊥ : Subgroup ↥(Y.Gi 1)) := by
      intro a ha
      have hcomm : a * x = x * a := Subgroup.mem_centralizer_iff.mp hxcent a ha
      rw [hcomm]
      simp
    have hAZ : S ≤ Subgroup.normalizer (⊥ : Subgroup ↥(Y.Gi 1)) := by
      intro s _
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor <;> intro hh
      · rw [Subgroup.mem_bot] at hh ⊢
        rw [hh]; simp
      · rw [Subgroup.mem_bot] at hh ⊢
        have := congrArg (fun z => s⁻¹ * z * s) hh
        simpa [mul_assoc] using this
    exact CFSG.LocalAnalysis.EvenBN.Common.mem_of_mem_commutator_sup_of_fixed
      (A := S) (Y := M) (Z := ⊥) bot_le hMcomm hSM hAZ hcop hx' hfixx
  have hMmap : M.map (Subgroup.subtype (Y.Gi 1)) = X :=
    Subgroup.map_subgroupOf_eq_of_le hX
  have hCmap : (Subgroup.centralizer (S : Set ↥(Y.Gi 1))).map (Subgroup.subtype (Y.Gi 1))
      = Subgroup.centralizer ({d} : Set G) ⊓ Y.Gi 1 := by
    rw [map_centralizer_subgroupOf (Subgroup.zpowers_le.mpr hdG),
      centralizer_zpowers_eq_singleton]
  have hMap : (M ⊓ Subgroup.centralizer (S : Set ↥(Y.Gi 1))).map (Subgroup.subtype (Y.Gi 1))
      = X ⊓ Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.map_inf _ _ _ (Subtype.coe_injective), hMmap, hCmap]
    refine le_antisymm ?_ (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hX)))
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨hx.1, (Subgroup.mem_inf.mp hx.2).1⟩
  have hNmap : N.map (Subgroup.subtype (Y.Gi 1)) = ⁅X, Subgroup.zpowers d⁆ := by
    rw [show N = ⁅M, S⁆ from rfl, Subgroup.map_commutator, hMmap,
      Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr hdG)]
  refine ⟨?_, ?_⟩
  · have h := congrArg (Subgroup.map (Subgroup.subtype (Y.Gi 1))) hsupM
    rw [Subgroup.map_sup, hMap, hNmap, hMmap] at h
    exact h
  · have h := congrArg (Subgroup.map (Subgroup.subtype (Y.Gi 1))) hdisjM
    rw [Subgroup.map_inf _ _ _ (Subtype.coe_injective), hMap, hNmap, Subgroup.map_bot] at h
    exact h

private theorem Z_one_fitting_decomp (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {d : G}
    (hd : d ∈ Y.J 1) (hd3 : orderOf d = 3) :
    Y.Z 1 = (Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ ⁅Y.Z 1, Subgroup.zpowers d⁆ ∧
      (Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G)) ⊓ ⁅Y.Z 1, Subgroup.zpowers d⁆ = ⊥ := by
  have hdG : d ∈ Y.Gi 1 := Y.L_le_Gi 1 (Y.J_le_L 1 hd)
  have hZnorm : Subgroup.zpowers d ≤ Subgroup.normalizer (Y.Z 1 : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Y.Z_normal 1 d hdG
  have hZ1p : IsPGroup 2 (Y.Z 1) := (pCoreOf_isPGroup' (Y.Gi 1)).to_le (Y.Z_le_Q 1)
  exact abelian_fitting_decomp_of_zpowers (Y := Y) (X := Y.Z 1) (d := d) hdG hd3 hZnorm
    (Y.Z_le_Gi 1) hZ1p (fun x hx y hy => Y.Z_commute 1 x hx y hy)

private theorem conjSub_Qs (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {d : G} (hd : d ∈ Y.J 1) :
    conjSub d (Y.Qs 1) = Y.Qs 1 :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (J_one_le_normalizer_Qs_one Y H hd)

private theorem conjSub_commutator_Z_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {d : G}
    (hd : d ∈ Y.J 1) :
    conjSub d ⁅Y.Z 1, Subgroup.zpowers d⁆ = ⁅Y.Z 1, Subgroup.zpowers d⁆ := by
  have hdG : d ∈ Y.Gi 1 := Y.L_le_Gi 1 (Y.J_le_L 1 hd)
  change (⁅Y.Z 1, Subgroup.zpowers d⁆).map (MulAut.conj d).toMonoidHom = _
  rw [Subgroup.map_commutator]
  change ⁅conjSub d (Y.Z 1), conjSub d (Subgroup.zpowers d)⁆ = ⁅Y.Z 1, Subgroup.zpowers d⁆
  rw [Y.Z_normal 1 d hdG, conjSub_eq_of_mem (Subgroup.mem_zpowers d)]

private theorem commutator_Z_one_le_commutator_Qs (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (h3 : Y.Zt 1 = ⊥) {d : G} :
    ⁅Y.Z 1, Subgroup.zpowers d⁆ ≤ ⁅Y.Qs 1, Subgroup.zpowers d⁆ :=
  Subgroup.commutator_mono (Z_one_le_Qs_and_Q_zero Y H h3).1 le_rfl

private theorem commutator_Qs_inf_centralizer_eq_bot (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {d : G} (hd : d ∈ Y.J 1) (hd3 : orderOf d = 3) :
    ⁅Y.Qs 1, Subgroup.zpowers d⁆ ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ := by
  have hdG : d ∈ Y.Gi 1 := Y.L_le_Gi 1 (Y.J_le_L 1 hd)
  have hQsnorm : Subgroup.zpowers d ≤ Subgroup.normalizer (Y.Qs 1 : Set G) := by
    refine Subgroup.zpowers_le.mpr ?_
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (conjSub_Qs Y H hd)
  have hQsp : IsPGroup 2 (Y.Qs 1) :=
    (pCoreOf_isPGroup' (Y.Gi 1)).to_le (inf_le_left : Y.Qs 1 ≤ Y.Q 1)
  haveI hQcomm : IsMulCommutative (Y.Qs 1) := (goldschmidt_small_apply Y H hd hd3).1
  have hQsab : ∀ x ∈ Y.Qs 1, ∀ y ∈ Y.Qs 1, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (hQcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEQs : ⁅Y.Qs 1, Subgroup.zpowers d⁆ ≤ Y.Qs 1 := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hQsnorm
  have h := (abelian_fitting_decomp_of_zpowers (Y := Y) (X := Y.Qs 1) (d := d) hdG hd3
    hQsnorm ((inf_le_left : Y.Qs 1 ≤ Y.Q 1).trans (Y.Q_le_Gi 1)) hQsp hQsab).2
  rw [eq_bot_iff] at h ⊢
  intro x hx
  exact h (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hEQs hx.1, hx.2⟩, hx.1⟩)

private theorem commutator_Z_one_zpowers_le (Y : Setup Γ G) {d : G} (hd : d ∈ Y.J 1) :
    ⁅Y.Z 1, Subgroup.zpowers d⁆ ≤ Y.Z 1 :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr
    (Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (Y.Z_normal 1 d (Y.L_le_Gi 1 (Y.J_le_L 1 hd)))))

private theorem commutator_Z_one_eq_bot_or_eq_E (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (h3 : Y.Zt 1 = ⊥) {d : G} (hd : d ∈ Y.J 1) (hd3 : orderOf d = 3)
    (hE : Nat.card ↥⁅Y.Qs 1, Subgroup.zpowers d⁆ = 4) :
    ⁅Y.Z 1, Subgroup.zpowers d⁆ = ⊥ ∨
      ⁅Y.Z 1, Subgroup.zpowers d⁆ = ⁅Y.Qs 1, Subgroup.zpowers d⁆ := by
  set N : Subgroup G := ⁅Y.Z 1, Subgroup.zpowers d⁆
  set E : Subgroup G := ⁅Y.Qs 1, Subgroup.zpowers d⁆ with hEdef
  have hQsnorm : Subgroup.zpowers d ≤ Subgroup.normalizer (Y.Qs 1 : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (conjSub_Qs Y H hd))
  have hEQs : E ≤ Y.Qs 1 := by
    rw [hEdef, Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hQsnorm
  haveI hEfin : Finite ↥E := finite_of_le_stabilizer Y.hyp (H := E)
    (hEQs.trans ((inf_le_left : Y.Qs 1 ≤ Y.Q 1).trans (Y.Q_le_Gi 1)))
  have hNE : N ≤ E := commutator_Z_one_le_commutator_Qs Y H h3
  haveI hNfin : Finite ↥N :=
    Finite.of_injective (Subgroup.inclusion hNE) (Subgroup.inclusion_injective hNE)
  have hdvdpow : Nat.card ↥N ∣ 2 ^ 2 := by simpa using hE ▸ Subgroup.card_dvd_of_le hNE
  have hNinv : conjSub d N = N := conjSub_commutator_Z_one Y H hd
  have hdisj := (Z_one_fitting_decomp Y H hd hd3).2
  obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvdpow
  have hk_le2 : k ≤ 2 := by simpa using hk_le
  interval_cases k
  · left
    rw [Subgroup.eq_bot_iff_card]
    simpa using hk
  · exfalso
    have h2 : Nat.card ↥N = 2 := by simpa using hk
    have hNleCd : N ≤ Subgroup.centralizer ({d} : Set G) := by
      have hdC : d ∈ Subgroup.centralizer (N : Set G) := by
        rw [← CFSG.Quasithin.normalizer_eq_centralizer_of_card_eq_two h2]
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hNinv
      exact fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hdC x hx)
    have hNleZ : N ≤ Y.Z 1 := commutator_Z_one_zpowers_le Y hd
    have hle_bot : N ≤ (⊥ : Subgroup G) := by
      rw [← hdisj]
      exact le_inf (le_inf hNleZ hNleCd) le_rfl
    have hbot : N = ⊥ := le_bot_iff.mp hle_bot
    rw [hbot] at h2
    exact absurd h2 (by simp)
  · right
    have hk4 : Nat.card ↥N = 4 := by simpa using hk
    exact Subgroup.eq_of_le_of_card_ge hNE (by rw [hE]; omega)

private theorem Z_one_eq_sup_E (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (h3 : Y.Zt 1 = ⊥) {d : G}
    (hd : d ∈ Y.J 1) (hd3 : orderOf d = 3)
    (hEcard : Nat.card ↥⁅Y.Qs 1, Subgroup.zpowers d⁆ = 4)
    (hEZ : ⁅Y.Qs 1, Subgroup.zpowers d⁆ ≤ Y.Z 1) :
    Y.Z 1 = (Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ ⁅Y.Qs 1, Subgroup.zpowers d⁆ ∧
      (Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G)) ⊓ ⁅Y.Qs 1, Subgroup.zpowers d⁆ = ⊥ := by
  have hfit := Z_one_fitting_decomp Y H hd hd3
  have hcases := commutator_Z_one_eq_bot_or_eq_E Y H h3 hd hd3 hEcard
  have hNE : ⁅Y.Z 1, Subgroup.zpowers d⁆ = ⁅Y.Qs 1, Subgroup.zpowers d⁆ := by
    rcases hcases with hbot | hE
    · exfalso
      have hZle : Y.Z 1 ≤ Subgroup.centralizer ({d} : Set G) := by
        rw [hfit.1, hbot, sup_bot_eq]
        exact inf_le_right
      have hEle : ⁅Y.Qs 1, Subgroup.zpowers d⁆ ≤ Subgroup.centralizer ({d} : Set G) :=
        hEZ.trans hZle
      have hEqs : ⁅Y.Qs 1, Subgroup.zpowers d⁆ ≤ Y.Qs 1 := by
        rw [Subgroup.commutator_comm]
        refine Subgroup.le_normalizer_iff_commutator_le_right.mp ?_
        exact Subgroup.zpowers_le.mpr
          (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (conjSub_Qs Y H hd))
      have hdisjE := commutator_Qs_inf_centralizer_eq_bot Y H hd hd3
      have hbotE : ⁅Y.Qs 1, Subgroup.zpowers d⁆ ≤ (⊥ : Subgroup G) := by
        rw [← hdisjE]
        exact le_inf le_rfl hEle
      have hE0 : ⁅Y.Qs 1, Subgroup.zpowers d⁆ = ⊥ := le_bot_iff.mp hbotE
      rw [hE0] at hEcard
      simp at hEcard
    · exact hE
  rw [hNE] at hfit
  exact hfit

private theorem exists_t_S_not_Qs (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    ∃ t ∈ Y.S ⊓ Subgroup.centralizer (Y.K : Set G), t ∉ Y.Qs 1 := by
  have hSyl := St_sylow Y H
  have hrel : (Y.Qs 1).relIndex (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) = 2 := hSyl.2.1
  have hle : Y.Qs 1 ≤ Y.S ⊓ Subgroup.centralizer (Y.K : Set G) := by
    refine le_inf ?_ inf_le_right
    show Y.Q 1 ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.S
    rw [← Y.edgeSylow_zero]
    exact inf_le_left.trans (Y.Q_le_edgeSylow_right 1)
  have hne : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≠ Y.Qs 1 := by
    intro h
    rw [h, Subgroup.relIndex_self] at hrel
    norm_num at hrel
  have hnot : ¬ (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) ≤ Y.Qs 1 :=
    fun hsub => hne (le_antisymm hsub hle)
  obtain ⟨t, ht, htQ⟩ := Set.not_subset.mp hnot
  exact ⟨t, ht, htQ⟩

private theorem S_eq_sup_zpowers (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {t : G}
    (ht : t ∈ Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) (htQ : t ∉ Y.Qs 1) :
    Y.S = Subgroup.zpowers t ⊔ Y.Q 1 := by
  have htS : t ∈ Y.S := ht.1
  have htQ1 : t ∉ Y.Q 1 := by
    intro h
    exact htQ (Subgroup.mem_inf.mpr ⟨h, ht.2⟩)
  have hQ1S : (Y.Q 1).relIndex Y.S = 2 := by
    rw [← Y.edgeSylow_zero]
    simpa [H.n_one] using Y.relIndex_Q_succ_edgeSylow 0
  have hsup_le : Subgroup.zpowers t ⊔ Y.Q 1 ≤ Y.S := by
    refine sup_le (Subgroup.zpowers_le.mpr htS) ?_
    rw [← Y.edgeSylow_zero]
    exact Y.Q_le_edgeSylow_right 1
  have hQ1sup : Y.Q 1 ≤ Subgroup.zpowers t ⊔ Y.Q 1 := le_sup_right
  have hne : Subgroup.zpowers t ⊔ Y.Q 1 ≠ Y.Q 1 := by
    intro h
    exact htQ1 (h ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  exact ((CFSG.Quasithin.eq_or_eq_of_relIndex_prime Nat.prime_two hQ1sup hsup_le
    hQ1S).resolve_left hne).symm

private theorem Z_one_inf_centralizer_S_eq_sup (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (h3 : Y.Zt 1 = ⊥) {d t : G} (hd : d ∈ Y.J 1) (hd3 : orderOf d = 3)
    (hEcard : Nat.card ↥⁅Y.Qs 1, Subgroup.zpowers d⁆ = 4)
    (hEZ : ⁅Y.Qs 1, Subgroup.zpowers d⁆ ≤ Y.Z 1)
    (hA : Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G) = centerOf (Y.L 1))
    (ht : t ∈ Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) (htQ : t ∉ Y.Qs 1) :
    Y.Z 1 ⊓ Subgroup.centralizer (Y.S : Set G) =
      (Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
        (⁅Y.Qs 1, Subgroup.zpowers d⁆ ⊓ Subgroup.centralizer ({t} : Set G)) := by
  set A : Subgroup G := Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G) with hAdef
  set E : Subgroup G := ⁅Y.Qs 1, Subgroup.zpowers d⁆ with hEdef
  have hsupZ : Y.Z 1 = A ⊔ E := (Z_one_eq_sup_E Y H h3 hd hd3 hEcard hEZ).1
  have htS : t ∈ Y.S := ht.1
  have htJ : t ∈ Y.J 1 := (St_sylow Y H).1.1 ht
  have hJL : Y.J 1 ≤ Y.L 1 := Y.J_le_L 1
  have hS : Y.S = Subgroup.zpowers t ⊔ Y.Q 1 := S_eq_sup_zpowers Y H ht htQ
  have hSL : Y.S ≤ Y.L 1 := Y.S_le_L_one
  have hZ1Q1 : Y.Z 1 ≤ Subgroup.centralizer (Y.Q 1 : Set G) :=
    (Y.Z_le_center 1).trans inf_le_right
  have hACt : A ≤ Subgroup.centralizer ({t} : Set G) := by
    intro x hx
    have hx' : x ∈ centerOf (Y.L 1) := hA ▸ hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx').2 t (hJL htJ)).symm
  have hnormA : ∀ e ∈ Y.Z 1, ∀ a ∈ A, e * a * e⁻¹ ∈ A := by
    intro e he a ha
    have haZ : a ∈ Y.Z 1 := (Subgroup.mem_inf.mp ha).1
    have heq : e * a * e⁻¹ = a := by rw [Y.Z_commute 1 e he a haZ]; group
    rw [heq]
    exact ha
  have hAEnorm : E ≤ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro e he
    exact hnormA e (hEZ he)
  have hEnorm : (E ⊓ Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro e he
    exact hnormA e (hEZ (Subgroup.mem_inf.mp he).1)
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxZ, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxAE : x ∈ A ⊔ E := by rw [← hsupZ]; exact hxZ
    obtain ⟨a, ha, e, he, rfl⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hAEnorm).mp hxAE
    have haCt : a ∈ Subgroup.centralizer ({t} : Set G) := hACt ha
    have haeCt : a * e ∈ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htS) hxC
    have heCt : e ∈ Subgroup.centralizer ({t} : Set G) := by
      have ha' : a⁻¹ ∈ Subgroup.centralizer ({t} : Set G) :=
        (Subgroup.centralizer _).inv_mem haCt
      have h := (Subgroup.centralizer ({t} : Set G)).mul_mem ha' haeCt
      rwa [inv_mul_cancel_left] at h
    exact (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hEnorm).mpr
      ⟨a, ha, e, Subgroup.mem_inf.mpr ⟨he, heCt⟩, rfl⟩
  · refine sup_le ?_ ?_
    · intro x hx
      have hxZ : x ∈ Y.Z 1 := (Subgroup.mem_inf.mp hx).1
      have hx' : x ∈ centerOf (Y.L 1) := hA ▸ hx
      refine Subgroup.mem_inf.mpr ⟨hxZ, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx').2 y (hSL hy)
    · intro x hx
      obtain ⟨hxE, hxt⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨hEZ hxE, ?_⟩
      have hgen : Y.S ≤ Subgroup.centralizer ({x} : Set G) := by
        rw [hS]
        refine sup_le ?_ ?_
        · intro a ha
          rw [Subgroup.mem_centralizer_singleton_iff]
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
          exact (show Commute t x from
            (Subgroup.mem_centralizer_singleton_iff.mp hxt).symm).zpow_left n
        · intro b hb
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp (hZ1Q1 (hEZ hxE)) b hb)
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (hgen hy)

private theorem card_centerOf_S_eq_two_mul (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (h3 : Y.Zt 1 = ⊥)
    {d t : G} (hd : d ∈ Y.J 1) (hd3 : orderOf d = 3)
    (hEcard : Nat.card ↥⁅Y.Qs 1, Subgroup.zpowers d⁆ = 4)
    (hEZ : ⁅Y.Qs 1, Subgroup.zpowers d⁆ ≤ Y.Z 1)
    (hA : Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G) = centerOf (Y.L 1))
    (ht : t ∈ Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) (htQ : t ∉ Y.Qs 1)
    (htE : Nat.card ↥(⁅Y.Qs 1, Subgroup.zpowers d⁆ ⊓
      Subgroup.centralizer ({t} : Set G)) = 2) :
    Nat.card ↥(centerOf Y.S) = 2 * Nat.card ↥(Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G)) := by
  set A : Subgroup G := Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G) with hAdef
  set E : Subgroup G := ⁅Y.Qs 1, Subgroup.zpowers d⁆ with hEdef
  have hdisjZ : A ⊓ E = ⊥ := (Z_one_eq_sup_E Y H h3 hd hd3 hEcard hEZ).2
  have hnormA : ∀ e ∈ Y.Z 1, ∀ a ∈ A, e * a * e⁻¹ ∈ A := by
    intro e he a ha
    have haZ : a ∈ Y.Z 1 := (Subgroup.mem_inf.mp ha).1
    have heq : e * a * e⁻¹ = a := by rw [Y.Z_commute 1 e he a haZ]; group
    rw [heq]
    exact ha
  have hEnorm : (E ⊓ Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro e he
    exact hnormA e (hEZ (Subgroup.mem_inf.mp he).1)
  have hCeq := Z_one_inf_centralizer_S_eq_sup Y H h3 hd hd3 hEcard hEZ hA ht htQ
  have hcard := CFSG.LocalAnalysis.EvenBN.Common.card_sup_mul_card_inf_eq (A := A)
    (B := E ⊓ Subgroup.centralizer ({t} : Set G)) hEnorm
  have hdisj' : A ⊓ (E ⊓ Subgroup.centralizer ({t} : Set G)) = ⊥ := by
    rw [← inf_assoc, hdisjZ]
    simp
  rw [hdisj', htE] at hcard
  have hbot : Nat.card ↥(⊥ : Subgroup G) = 1 := by simp
  rw [hbot, mul_one] at hcard
  have hcenter : centerOf Y.S = Y.Z 1 ⊓ Subgroup.centralizer (Y.S : Set G) :=
    ((center_S_le_Z Y H 1 (Or.inr rfl)).2).symm
  rw [hcenter, hCeq, hcard]
  omega


private theorem isSylowTwoOf_S_Gi_zero (Y : Setup Γ G) : IsSylowTwoOf Y.S (Y.Gi 0) := by
  simpa [Setup.S, Setup.edgeSylow] using
    isSylowTwoOf_of_edgeStab Y.hyp (Y.adj 0) (Y.isSylowTwoOf_edgeSylow 0)

private theorem Zt_zero_eq_bot_of_le_centralizer (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (h : centerOf Y.S ≤ Subgroup.centralizer (Y.edgeSylow (-1) : Set G)) :
    Y.Zt 0 = ⊥ := by
  have hPleZ0 : centerOf Y.S ≤ Y.Z 0 := (center_S_le_Z Y H 0 (Or.inl rfl)).1
  have hPleCS : centerOf Y.S ≤ Subgroup.centralizer (Y.S : Set G) := by
    rw [← (center_S_le_Z Y H 0 (Or.inl rfl)).2]
    exact inf_le_right
  have hPleL0 : centerOf Y.S ≤ Y.L 0 := fun x hx =>
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (Y.Gi 0)) (Y.Q_le_Gi 0)
      ((hPleZ0.trans (Y.Z_le_Q 0)) hx)
  have hPleZL0 : centerOf Y.S ≤ centerOf (Y.L 0) := by
    refine le_inf hPleL0 ?_
    have hgen : Y.L 0 = Y.S ⊔ Y.edgeSylow (-1) := by
      rw [show Y.S = Y.edgeSylow 0 from Y.edgeSylow_zero.symm, sup_comm]
      simpa using (Y.edgeSylow_sup_edgeSylow 0).symm
    have hS1 : Y.S ≤ Subgroup.centralizer (centerOf Y.S : Set G) :=
      Subgroup.le_centralizer_iff.mp hPleCS
    have hS2 : Y.edgeSylow (-1) ≤ Subgroup.centralizer (centerOf Y.S : Set G) :=
      Subgroup.le_centralizer_iff.mp h
    have hsup : Y.S ⊔ Y.edgeSylow (-1) ≤
        Subgroup.centralizer (centerOf Y.S : Set G) := sup_le hS1 hS2
    rw [← hgen] at hsup
    exact Subgroup.le_centralizer_iff.mpr hsup
  have hSyl0 : IsSylowTwoOf Y.S (Y.Gi 0) := isSylowTwoOf_S_Gi_zero Y
  have hL0C : Y.L 0 ≤ Subgroup.centralizer (centerOf Y.S : Set G) := by
    have h1 : centerOf Y.S ≤ Subgroup.centralizer (Y.L 0 : Set G) :=
      hPleZL0.trans inf_le_right
    exact Subgroup.le_centralizer_iff.mp h1
  have hZ0eq : Y.Z 0 = centerOf (Y.L 0) :=
    (Y.Z_eq_centerOf_of_centralizes H.char 0 hSyl0 hL0C).2
  rw [Setup.Zt, hZ0eq, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 k
    (Y.K_le_L_zero H hk)

private theorem two_mul_card_le_card_sup_of_card_eq {P Q : Subgroup G} [Finite ↥P]
    [Finite ↥Q] (hQP : Q ≤ Subgroup.normalizer (P : Set G))
    (hcard : Nat.card ↥Q = Nat.card ↥P) (hne : P ≠ Q) :
    2 * Nat.card ↥P ≤ Nat.card ↥(P ⊔ Q) := by
  have hcardPQ := CFSG.LocalAnalysis.EvenBN.Common.card_sup_mul_card_inf_eq
    (A := P) (B := Q) hQP
  have hproper : P ⊓ Q ≠ P := by
    intro hEq
    have hPQ : P ≤ Q := hEq ▸ inf_le_right
    exact hne (Subgroup.eq_of_le_of_card_ge hPQ (le_of_eq hcard))
  have hrel : 2 ≤ (P ⊓ Q).relIndex P := by
    have hne1 : (P ⊓ Q).relIndex P ≠ 1 := fun h1 =>
      hproper (le_antisymm inf_le_left (Subgroup.relIndex_eq_one.mp h1))
    have hpos : 0 < (P ⊓ Q).relIndex P := by
      have hmul := Subgroup.relIndex_mul_card (H := P ⊓ Q) (K := P)
      by_contra h
      rw [Nat.not_lt] at h
      have h0 : (P ⊓ Q).relIndex P = 0 := Nat.eq_zero_of_le_zero h
      rw [h0, zero_mul] at hmul
      exact Nat.card_pos.ne' hmul.symm
    omega
  have hrelcard : (P ⊓ Q).relIndex P * Nat.card ↥(P ⊓ Q) = Nat.card ↥P := by
    have h := Subgroup.relIndex_mul_card (H := P ⊓ Q) (K := P)
    rwa [inf_of_le_left inf_le_left] at h
  have h2 : 2 * Nat.card ↥(P ⊓ Q) ≤ Nat.card ↥P := by
    calc 2 * Nat.card ↥(P ⊓ Q) ≤ (P ⊓ Q).relIndex P * Nat.card ↥(P ⊓ Q) :=
          Nat.mul_le_mul_right _ hrel
      _ = Nat.card ↥P := hrelcard
  have hPQcard : Nat.card ↥(P ⊔ Q) * Nat.card ↥(P ⊓ Q) = Nat.card ↥P * Nat.card ↥P := by
    rw [hcardPQ, hcard]
  have hstep : 2 * (Nat.card ↥P * Nat.card ↥P) ≤ Nat.card ↥(P ⊔ Q) * Nat.card ↥P := by
    calc 2 * (Nat.card ↥P * Nat.card ↥P)
        = 2 * (Nat.card ↥(P ⊔ Q) * Nat.card ↥(P ⊓ Q)) := by rw [hPQcard]
      _ = Nat.card ↥(P ⊔ Q) * (2 * Nat.card ↥(P ⊓ Q)) := by ring
      _ ≤ Nat.card ↥(P ⊔ Q) * Nat.card ↥P := Nat.mul_le_mul_left _ h2
  have hstep' : Nat.card ↥P * (2 * Nat.card ↥P) ≤ Nat.card ↥P * Nat.card ↥(P ⊔ Q) := by
    calc Nat.card ↥P * (2 * Nat.card ↥P) = 2 * (Nat.card ↥P * Nat.card ↥P) := by ring
      _ ≤ Nat.card ↥(P ⊔ Q) * Nat.card ↥P := hstep
      _ = Nat.card ↥P * Nat.card ↥(P ⊔ Q) := by ring
  exact Nat.le_of_mul_le_mul_left hstep' Nat.card_pos

private theorem card_centralizer_Z0_K_ge (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) :
    2 * Nat.card ↥(centerOf Y.S) ≤
      Nat.card ↥(Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G)) := by
  obtain ⟨g, hg, hgm⟩ := Y.exists_normalizer_K_move 0 (Y.K_le_L_zero H) (Y.L_le_Gi 0)
    (fun a b ha hb => (Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).trans a b ha hb)
    (Y.adj 0) (by have := Y.adj (-1); simpa using this.symm)
    (fun k hk => Y.K_fix k hk 1) (fun k hk => Y.K_fix k hk (-1))
  obtain ⟨hgL, hgN⟩ := Subgroup.mem_inf.mp hg
  let h : G := g⁻¹
  have hhL : h ∈ Y.L 0 := (Y.L 0).inv_mem hgL
  have hhN : h ∈ Subgroup.normalizer (Y.K : Set G) :=
    (Subgroup.normalizer (Y.K : Set G)).inv_mem hgN
  have hh0 : h • Y.vert 0 = Y.vert 0 := MulAction.mem_stabilizer_iff.mp (Y.L_le_Gi 0 hhL)
  have hh1 : h • Y.vert 1 = Y.vert (-1) := by
    have hg0 : g • Y.vert 0 = Y.vert 0 := MulAction.mem_stabilizer_iff.mp (Y.L_le_Gi 0 hgL)
    have := congrArg (fun w => g⁻¹ • w) hgm
    simpa [h, hg0] using this.symm
  have hGi0 : conjSub h (Y.Gi 0) = Y.Gi 0 := by
    rw [← stabilizer_smul_eq_conjSub, hh0]
  have hGi1 : conjSub h (Y.Gi 1) = Y.Gi (-1) := by
    rw [← stabilizer_smul_eq_conjSub, hh1]
  have hSconj : conjSub h Y.S = Y.edgeSylow (-1) := by
    unfold Setup.S
    rw [show Y.edgeSylow (-1) = pCoreOf 2 (Y.Gi (-1) ⊓ Y.Gi ((-1) + 1)) from rfl]
    rw [← pCoreOf_conjSub, conjSub_inf, hGi0, hGi1, show (-1 : ℤ) + 1 = 0 by ring, inf_comm]
  have hcenth : conjSub h (Subgroup.centralizer (Y.S : Set G)) =
      Subgroup.centralizer (Y.edgeSylow (-1) : Set G) := by
    rw [← conjSub_centralizer h Y.S, hSconj]
  let P : Subgroup G := centerOf Y.S
  let Q : Subgroup G := conjSub h P
  haveI : Finite ↥(Y.Gi 0) := Y.hyp.finite_stab (Y.vert 0)
  have hZ1K : Y.Z 1 ≤ Subgroup.centralizer (Y.K : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  have hPleZ0 : P ≤ Y.Z 0 := (center_S_le_Z Y H 0 (Or.inl rfl)).1
  have hPleCS : P ≤ Subgroup.centralizer (Y.S : Set G) := by
    calc P = centerOf Y.S := rfl
      _ = Y.Z 0 ⊓ Subgroup.centralizer (Y.S : Set G) :=
          (center_S_le_Z Y H 0 (Or.inl rfl)).2.symm
      _ ≤ Subgroup.centralizer (Y.S : Set G) := inf_le_right
  have hPleC0 : P ≤ Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) :=
    le_inf hPleZ0 (((center_S_le_Z Y H 1 (Or.inr rfl)).1).trans hZ1K)
  have hQleC0 : Q ≤ Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) := by
    refine le_inf ?_ ?_
    · rw [show Q = conjSub h P from rfl]
      calc conjSub h P ≤ conjSub h (Y.Z 0) := conjSub_mono h hPleZ0
        _ = Y.Z 0 := Y.Z_normal 0 h (Y.L_le_Gi 0 hhL)
    · rw [show Q = conjSub h P from rfl]
      calc conjSub h P ≤ conjSub h (Subgroup.centralizer (Y.K : Set G)) :=
            conjSub_mono h (((center_S_le_Z Y H 1 (Or.inr rfl)).1).trans hZ1K)
        _ = Subgroup.centralizer (Y.K : Set G) := by
            have hK : conjSub h Y.K = Y.K :=
              Subgroup.mem_normalizer_iff_map_conj_eq.mp hhN
            rw [← conjSub_centralizer h Y.K, hK]
  haveI hPfin : Finite ↥P :=
    Finite.of_injective (Subgroup.inclusion (hPleC0.trans (inf_le_left.trans (Y.Z_le_Gi 0))))
      (Subgroup.inclusion_injective _)
  haveI hQfin : Finite ↥Q :=
    Finite.of_injective (Subgroup.inclusion (hQleC0.trans (inf_le_left.trans (Y.Z_le_Gi 0))))
      (Subgroup.inclusion_injective _)
  have hQleCSh : Q ≤ Subgroup.centralizer (Y.edgeSylow (-1) : Set G) := by
    rw [show Q = conjSub h P from rfl]
    calc conjSub h P ≤ conjSub h (Subgroup.centralizer (Y.S : Set G)) := conjSub_mono h hPleCS
      _ = Subgroup.centralizer (Y.edgeSylow (-1) : Set G) := hcenth
  have hPne : P ≠ Q := by
    intro hPQ
    have hPleCSh : P ≤ Subgroup.centralizer (Y.edgeSylow (-1) : Set G) := hPQ ▸ hQleCSh
    exact hZ (Zt_zero_eq_bot_of_le_centralizer Y H hPleCSh)
  have hC0ab : ∀ a ∈ Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G),
      ∀ b ∈ Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G), a * b = b * a := by
    intro a ha b hb
    exact Y.Z_commute 0 a (Subgroup.mem_inf.mp ha).1 b (Subgroup.mem_inf.mp hb).1
  have hQnorm : Q ≤ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro q hq p hp
    have heq : q * p * q⁻¹ = p := by
      rw [hC0ab q (hQleC0 hq) p (hPleC0 hp)]; group
    rw [heq]
    exact hp
  have hQcard : Nat.card ↥Q = Nat.card ↥P := by
    rw [show Q = P.map (MulAut.conj h).toMonoidHom from rfl]
    exact Subgroup.card_map_of_injective (MulEquiv.injective _)
  have h2P := two_mul_card_le_card_sup_of_card_eq (P := P) (Q := Q) hQnorm hQcard hPne
  haveI : Finite ↥(Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G)) :=
    finite_of_le_stabilizer Y.hyp (H := Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G))
      (inf_le_left.trans (Y.Z_le_Gi 0))
  exact le_trans h2P (Nat.card_le_card_of_injective _
    (Subgroup.inclusion_injective (sup_le hPleC0 hQleC0)))

private theorem card_Z_one_of_eq_center (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1)) : Nat.card (Y.Z 1) = 2 := by
  obtain ⟨d, hdJ, hd3⟩ := exists_J_three Y H
  haveI hGifin : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  have hZ1Qs : Y.Z 1 ≤ Y.Qs 1 := (Z_one_le_Qs_and_Q_zero Y H h3).1
  have hZ1CJ : Y.Z 1 ≤ Subgroup.centralizer (Y.J 1 : Set G) := by
    rw [h4]
    intro z hz
    exact Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr (oTwoPrime_mono (inf_le_right : Y.N ⊓ Y.Gi 1 ≤ Y.Gi 1)))
      (Subgroup.mem_inf.mp hz).2
  have hZ1Cd : Y.Z 1 ≤ Subgroup.centralizer ({d} : Set G) :=
    hZ1CJ.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdJ))
  haveI hZ1fin : Finite ↥(Y.Z 1) := finite_of_le_stabilizer Y.hyp (H := Y.Z 1) (Y.Z_le_Gi 1)
  have hle : Nat.card (Y.Z 1) ≤ 2 := by
    haveI : Finite ↥(Y.Qs 1 ⊓ Subgroup.centralizer ({d} : Set G)) :=
      Finite.of_injective
        (Subgroup.inclusion (show Y.Qs 1 ⊓ Subgroup.centralizer ({d} : Set G) ≤ Y.Gi 1 from
          inf_le_left.trans ((inf_le_left : Y.Qs 1 ≤ Y.Q 1).trans (Y.Q_le_Gi 1))))
        (Subgroup.inclusion_injective _)
    have hsub : Y.Z 1 ≤ Y.Qs 1 ⊓ Subgroup.centralizer ({d} : Set G) := le_inf hZ1Qs hZ1Cd
    exact le_trans (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hsub))
      (card_Qs_inf_centralizer Y H hdJ hd3)
  have hne : Y.Z 1 ≠ ⊥ := Y.Z_ne_bot_of 1 (Y.Q_ne_bot H.char 1)
  have hpos : 0 < Nat.card (Y.Z 1) := Nat.card_pos
  have hgt : 1 < Nat.card (Y.Z 1) := by
    have h1 : Nat.card (Y.Z 1) ≠ 1 := fun hc => hne (Subgroup.card_eq_one.mp hc)
    omega
  exact le_antisymm hle (Nat.succ_le_of_lt hgt)

private theorem four_le_card_Qs (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {d : G}
    (hd : d ∈ Y.J 1) (hd3 : orderOf d = 3)
    (hEcard : Nat.card ↥⁅Y.Qs 1, Subgroup.zpowers d⁆ = 4) :
    4 ≤ Nat.card (Y.Qs 1) := by
  haveI : Finite ↥(Y.Qs 1) := finite_of_le_stabilizer Y.hyp (α := Y.vert 1) (H := Y.Qs 1)
    ((inf_le_left : Y.Qs 1 ≤ Y.Q 1).trans (Y.Q_le_Gi 1))
  have hEQs : ⁅Y.Qs 1, Subgroup.zpowers d⁆ ≤ Y.Qs 1 := by
    rw [Subgroup.commutator_comm]
    refine Subgroup.le_normalizer_iff_commutator_le_right.mp ?_
    exact Subgroup.zpowers_le.mpr
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (conjSub_Qs Y H hd))
  have hdvd : 4 ∣ Nat.card (Y.Qs 1) := by
    have h := Subgroup.card_dvd_of_le hEQs
    rwa [hEcard] at h
  exact Nat.le_of_dvd Nat.card_pos hdvd

private theorem Z_one_eq_centerOf_L_one_of_commutator_eq_bot (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (h3 : Y.Zt 1 = ⊥) {d : G} (hd : d ∈ Y.J 1) (hd3 : orderOf d = 3)
    (hEcard : Nat.card ↥⁅Y.Qs 1, Subgroup.zpowers d⁆ = 4)
    (hNbot : ⁅Y.Z 1, Subgroup.zpowers d⁆ = ⊥) : Y.Z 1 = centerOf (Y.L 1) := by
  have hfit := Z_one_fitting_decomp Y H hd hd3
  have hZeqA : Y.Z 1 = Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G) := by
    have h2 := hfit.1
    rw [hNbot, sup_bot_eq] at h2
    exact h2
  have hZleCd : Y.Z 1 ≤ Subgroup.centralizer ({d} : Set G) := by
    rw [hZeqA]
    exact inf_le_right
  have hZ1Qs : Y.Z 1 ≤ Y.Qs 1 := (Z_one_le_Qs_and_Q_zero Y H h3).1
  have h4le : 4 ≤ Nat.card (Y.Qs 1) := four_le_card_Qs Y H hd hd3 hEcard
  have hCeq : Y.Qs 1 ⊓ Subgroup.centralizer ({d} : Set G) =
      Y.Qs 1 ⊓ Subgroup.centralizer (Y.J 1 : Set G) :=
    ((goldschmidt_small_apply Y H hd hd3).2.2.2 h4le).2.2.1
  have hZleCJ : Y.Z 1 ≤ Subgroup.centralizer (Y.J 1 : Set G) := by
    have h1 : Y.Z 1 ≤ Y.Qs 1 ⊓ Subgroup.centralizer (Y.J 1 : Set G) := by
      rw [← hCeq]
      exact le_inf hZ1Qs hZleCd
    exact h1.trans inf_le_right
  have : Y.Z 1 ≤ centerOf (Y.L 1) := by
    rw [centerOf_L_one_eq Y H]
    exact le_inf le_rfl hZleCJ
  exact Z_eq_center_of_le Y 1 this

private theorem Z_one_inf_centralizer_eq_centerOf_L_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (h3 : Y.Zt 1 = ⊥) {d : G} (hd : d ∈ Y.J 1) (hd3 : orderOf d = 3)
    (hEcard : Nat.card ↥⁅Y.Qs 1, Subgroup.zpowers d⁆ = 4) :
    Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G) = centerOf (Y.L 1) := by
  have hZ1Qs : Y.Z 1 ≤ Y.Qs 1 := (Z_one_le_Qs_and_Q_zero Y H h3).1
  have hlarge := (goldschmidt_small_apply Y H hd hd3).2.2.2
    (four_le_card_Qs Y H hd hd3 hEcard)
  have hCeqQs : Y.Qs 1 ⊓ Subgroup.centralizer ({d} : Set G) =
      Y.Qs 1 ⊓ Subgroup.centralizer (Y.J 1 : Set G) := hlarge.2.2.1
  rw [centerOf_L_one_eq Y H]
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨hzZ, hzd⟩ := Subgroup.mem_inf.mp hz
    have hmem : z ∈ Y.Qs 1 ⊓ Subgroup.centralizer ({d} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hZ1Qs hzZ, hzd⟩
    rw [hCeqQs] at hmem
    exact Subgroup.mem_inf.mpr ⟨hzZ, (Subgroup.mem_inf.mp hmem).2⟩
  · intro z hz
    obtain ⟨hzZ, hzJ⟩ := Subgroup.mem_inf.mp hz
    exact Subgroup.mem_inf.mpr ⟨hzZ,
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hd) hzJ⟩

private theorem card_mul_card_Z_zero_inf_centralizer_le (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {d : G} (hd : d ∈ Y.J 1) (hd3 : orderOf d = 3)
    (hZ0Q1 : Y.Z 0 ≤ Y.Q 1)
    (hA : Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G) = centerOf (Y.L 1)) :
    Nat.card ↥(Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G)) *
      Nat.card ↥(Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G)) ≤
      Nat.card ↥(Y.Qs 1) *
        Nat.card ↥(Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G)) := by
  obtain ⟨j, hjJ, hj0⟩ := J_trans Y H (Y.vert 0) (Y.vert 2) (Y.adj 0).symm (Y.adj 1)
  have hJN : Y.J 1 ≤ Subgroup.normalizer (Y.K : Set G) :=
    (oTwoPrime_le (Y.N ⊓ Y.Gi 1)).trans inf_le_left
  have hJG : Y.J 1 ≤ Y.Gi 1 := (oTwoPrime_le (Y.N ⊓ Y.Gi 1)).trans inf_le_right
  have hjN : j ∈ Subgroup.normalizer (Y.K : Set G) := hJN hjJ
  have hjG : j ∈ Y.Gi 1 := hJG hjJ
  have hKconj : conjSub j (Y.K : Subgroup G) = Y.K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hjN
  have hZ2 : Y.Z 2 = conjSub j (Y.Z 0) := Setup.Z_smul Y Y hj0
  let C0 : Subgroup G := Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G)
  let C2 : Subgroup G := Y.Z 2 ⊓ Subgroup.centralizer (Y.K : Set G)
  haveI hGifin : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  have hC0def : C0 = Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) := rfl
  have hC2def : C2 = Y.Z 2 ⊓ Subgroup.centralizer (Y.K : Set G) := rfl
  have hC2eq : C2 = conjSub j C0 := by
    rw [hC2def, hC0def, hZ2, conjSub_inf, ← conjSub_centralizer j Y.K, hKconj]
  have hQ1conj : conjSub j (Y.Q 1) = Y.Q 1 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1) hjG)
  have hC2Q1 : Y.Z 2 ≤ Y.Q 1 := by
    rw [hZ2]
    calc conjSub j (Y.Z 0) ≤ conjSub j (Y.Q 1) := conjSub_mono j hZ0Q1
      _ = Y.Q 1 := hQ1conj
  have hC0leQs : C0 ≤ Y.Qs 1 := by
    rw [hC0def]
    exact le_inf (inf_le_left.trans hZ0Q1) inf_le_right
  have hC2leQs : C2 ≤ Y.Qs 1 := by
    rw [hC2def]
    exact le_inf (inf_le_left.trans hC2Q1) inf_le_right
  haveI hC0fin : Finite ↥C0 :=
    Finite.of_injective
      (Subgroup.inclusion (hC0leQs.trans ((inf_le_left : Y.Qs 1 ≤ Y.Q 1).trans (Y.Q_le_Gi 1))))
      (Subgroup.inclusion_injective _)
  haveI hC2fin : Finite ↥C2 :=
    Finite.of_injective
      (Subgroup.inclusion (hC2leQs.trans ((inf_le_left : Y.Qs 1 ≤ Y.Q 1).trans (Y.Q_le_Gi 1))))
      (Subgroup.inclusion_injective _)
  haveI hC0C2fin : Finite ↥(C0 ⊔ C2) :=
    Finite.of_injective
      (Subgroup.inclusion (sup_le hC0leQs hC2leQs |>.trans
        ((inf_le_left : Y.Qs 1 ≤ Y.Q 1).trans (Y.Q_le_Gi 1))))
      (Subgroup.inclusion_injective _)
  haveI hC0infC2fin : Finite ↥(C0 ⊓ C2) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  haveI hAfin : Finite ↥(Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G)) :=
    Finite.of_injective
      (Subgroup.inclusion (inf_le_left.trans (Y.Z_le_Gi 1))) (Subgroup.inclusion_injective _)
  haveI hQsfin : Finite ↥(Y.Qs 1) := finite_of_le_stabilizer Y.hyp (α := Y.vert 1) (H := Y.Qs 1)
    ((inf_le_left : Y.Qs 1 ≤ Y.Q 1).trans (Y.Q_le_Gi 1))
  have hC2card : Nat.card ↥C2 = Nat.card ↥C0 := by
    rw [hC2eq]
    exact Subgroup.card_map_of_injective (MulEquiv.injective _)
  haveI hQcomm : IsMulCommutative (Y.Qs 1) := (goldschmidt_small_apply Y H hd hd3).1
  have hQsab : ∀ a ∈ Y.Qs 1, ∀ b ∈ Y.Qs 1, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hQcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hC2norm : C2 ≤ Subgroup.normalizer (C0 : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro q hq p hp
    have hqQs : q ∈ Y.Qs 1 := hC2leQs hq
    have hpQs : p ∈ Y.Qs 1 := hC0leQs hp
    have heq : q * p * q⁻¹ = p := by rw [hQsab q hqQs p hpQs]; group
    rw [heq]
    exact hp
  have hcardC0C2 := CFSG.LocalAnalysis.EvenBN.Common.card_sup_mul_card_inf_eq
    (A := C0) (B := C2) hC2norm
  have hC0C2card : Nat.card ↥(C0 ⊔ C2) * Nat.card ↥(C0 ⊓ C2) =
      Nat.card ↥C0 * Nat.card ↥C0 := by
    rw [hcardC0C2, hC2card]
  have hsupcard : Nat.card ↥(C0 ⊔ C2) ≤ Nat.card ↥(Y.Qs 1) :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective (sup_le hC0leQs hC2leQs))
  have hC0sq : Nat.card ↥C0 * Nat.card ↥C0 ≤
      Nat.card ↥(Y.Qs 1) * Nat.card ↥(C0 ⊓ C2) := by
    rw [← hC0C2card]
    exact Nat.mul_le_mul_right _ hsupcard
  have hC0C2center : C0 ⊓ C2 ≤ centerOf (Y.L 1) := by
    refine (le_inf ?_ ?_).trans (Y.Z_zero_inf_Z_two_le_centerOf H)
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_right.trans inf_le_left
  have hC0C2A : C0 ⊓ C2 ≤ Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G) := by
    rw [hA]
    exact hC0C2center
  have hinfcard : Nat.card ↥(C0 ⊓ C2) ≤
      Nat.card ↥(Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G)) :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hC0C2A)
  exact hC0sq.trans (Nat.mul_le_mul_left _ hinfcard)

private theorem false_of_E_le (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) {d : G} (hd : d ∈ Y.J 1) (hd3 : orderOf d = 3)
    (hEcard : Nat.card ↥⁅Y.Qs 1, Subgroup.zpowers d⁆ = 4)
    (hZ0Q1 : Y.Z 0 ≤ Y.Q 1)
    (hEZ : ⁅Y.Qs 1, Subgroup.zpowers d⁆ ≤ Y.Z 1) : False := by
  have hAcenter := Z_one_inf_centralizer_eq_centerOf_L_one Y H h3 hd hd3 hEcard
  obtain ⟨t, ht, htQ⟩ := exists_t_S_not_Qs Y H
  have hlarge := (goldschmidt_small_apply Y H hd hd3).2.2.2
    (four_le_card_Qs Y H hd hd3 hEcard)
  have htE : Nat.card ↥(⁅Y.Qs 1, Subgroup.zpowers d⁆ ⊓
      Subgroup.centralizer ({t} : Set G)) = 2 := hlarge.2.2.2.2 t ht htQ
  have hcardS := card_centerOf_S_eq_two_mul Y H h3 hd hd3 hEcard hEZ hAcenter ht htQ htE
  have hcardC0 := card_centralizer_Z0_K_ge Y H hZ h3
  have hC0ge : 4 * Nat.card ↥(Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G)) ≤
      Nat.card ↥(Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G)) := by
    rw [show 4 * Nat.card ↥(Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G)) =
      2 * Nat.card ↥(centerOf Y.S) by rw [hcardS]; ring]
    exact hcardC0
  have hC0sqA := card_mul_card_Z_zero_inf_centralizer_le Y H hd hd3 hZ0Q1 hAcenter
  have hQsle : Nat.card ↥(Y.Qs 1) ≤ 8 := card_Qs_le Y H
  have hfin : 16 * (Nat.card ↥(Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G)) *
      Nat.card ↥(Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G))) ≤
      8 * Nat.card ↥(Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G)) := by
    calc 16 * (Nat.card ↥(Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G)) *
          Nat.card ↥(Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G)))
        = (4 * Nat.card ↥(Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G))) *
          (4 * Nat.card ↥(Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G))) := by ring
      _ ≤ Nat.card ↥(Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G)) *
          Nat.card ↥(Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G)) :=
        Nat.mul_le_mul hC0ge hC0ge
      _ ≤ Nat.card ↥(Y.Qs 1) * Nat.card ↥(Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G)) :=
        hC0sqA
      _ ≤ 8 * Nat.card ↥(Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G)) :=
        Nat.mul_le_mul_right _ hQsle
  haveI : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  haveI : Finite ↥(Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G)) :=
    Finite.of_injective
      (Subgroup.inclusion (inf_le_left.trans (Y.Z_le_Gi 1))) (Subgroup.inclusion_injective _)
  have hApos : 0 < Nat.card ↥(Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G)) := Nat.card_pos
  have h16 : 16 * Nat.card ↥(Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G)) ≤ 8 :=
    Nat.le_of_mul_le_mul_right (by simpa [mul_assoc] using hfin) hApos
  have hAge : 16 ≤ 16 * Nat.card ↥(Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G)) := by
    have h1 : 1 ≤ Nat.card ↥(Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G)) :=
      Nat.succ_le_of_lt hApos
    simpa using Nat.mul_le_mul_left 16 h1
  omega

private theorem four_le_card_Qs_of_not_le (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hQ : ¬ Nat.card (Y.Qs 1) ≤ 2) : 4 ≤ Nat.card (Y.Qs 1) := by
  haveI : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  haveI : Finite ↥(Y.Qs 1) := finite_of_le_stabilizer Y.hyp (α := Y.vert 1) (H := Y.Qs 1)
    ((inf_le_left : Y.Qs 1 ≤ Y.Q 1).trans (Y.Q_le_Gi 1))
  have hQsp : IsPGroup 2 (Y.Qs 1) :=
    (pCoreOf_isPGroup' (Y.Gi 1)).to_le (inf_le_left : Y.Qs 1 ≤ Y.Q 1)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQsp
  have hQgt : 2 < Nat.card (Y.Qs 1) := Nat.lt_of_not_le hQ
  have hn2 : 2 ≤ n := by
    by_contra h
    have hle : n ≤ 1 := by omega
    interval_cases n
    · simp [hn] at hQgt
    · simp [hn] at hQgt
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    _ = Nat.card (Y.Qs 1) := hn.symm

private theorem Zt_not_le_Gi_neg_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (he : Y.ZtExt 0 r₀ r₀) : ¬ Y.Zt (r₀ : ℤ) ≤ Y.Gi (-1) := by
  obtain ⟨k, hk⟩ := (s52_step1 Y H hZ he).2
  have hm : (r₀ : ℤ) = 2 * (k : ℤ) := by
    have h : (r₀ : ℤ) = (k : ℤ) + (k : ℤ) := by exact_mod_cast hk
    linarith
  have hZt : Y.Zt (r₀ : ℤ) = conjSub (Y.τ ^ (k : ℤ)) (Y.Zt 0) := by
    rw [hm]
    simpa [conjSub] using Y.Zt_add_two 0 (k : ℤ)
  intro hle
  apply he.2.2
  have hconj : conjSub (Y.τ ^ (k : ℤ))⁻¹ (Y.Zt (r₀ : ℤ)) ≤
      conjSub (Y.τ ^ (k : ℤ))⁻¹ (Y.Gi (-1)) := conjSub_mono _ hle
  rw [hZt, conjSub_conjSub_inv] at hconj
  have hGi : conjSub (Y.τ ^ (k : ℤ))⁻¹ (Y.Gi (-1)) = Y.Gi (-1 - 2 * (k : ℤ)) := by
    have h := Y.Gi_add (-(k : ℤ)) (-1)
    have harg : -1 + 2 * (-(k : ℤ)) = -1 - 2 * (k : ℤ) := by ring
    rw [harg] at h
    rw [show (Y.τ ^ (k : ℤ))⁻¹ = Y.τ ^ (-(k : ℤ)) by group]
    exact h.symm
  rw [hGi] at hconj
  have harg2 : (-1 - 2 * (k : ℤ)) = (0 : ℤ) - (r₀ : ℤ) - 1 := by rw [hm]; ring
  rwa [harg2] at hconj

private theorem S_eq_Zt_sup_Q_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (he : Y.ZtExt 0 r₀ r₀) :
    Y.S = Y.Zt (r₀ : ℤ) ⊔ Y.Q 0 := by
  obtain ⟨k, hk⟩ := (s52_step1 Y H hZ he).2
  have hm : (r₀ : ℤ) = 2 * (k : ℤ) := by
    have h : (r₀ : ℤ) = (k : ℤ) + (k : ℤ) := by exact_mod_cast hk
    linarith
  have hr1 := he.one_le.1
  have hUr : Y.Zt (r₀ : ℤ) ≤ Y.Gi 1 := by
    have h := he.Zt_two_mul_le_Gi (k : ℤ) (1 - (r₀ : ℤ))
      (by omega) (by omega)
    have harg : 2 * (k : ℤ) + (1 - (r₀ : ℤ)) = 1 := by linarith
    rw [harg] at h
    rwa [← hm] at h
  have hUr0 : Y.Zt (r₀ : ℤ) ≤ Y.Gi 0 := he.Zt_le_Gi_zero ⟨k, hk⟩
  have hQneg : Y.Q 0 ≤ Y.Gi (-1) :=
    by simpa using (Y.Q_le_Gi_adj 0).trans inf_le_left
  have hnotQ : ¬ Y.Zt (r₀ : ℤ) ≤ Y.Q 0 := fun hQ =>
    Zt_not_le_Gi_neg_one Y H hZ he (hQ.trans hQneg)
  have hU2 : IsPGroup 2 (Y.Zt (r₀ : ℤ)) := Y.isPGroup_Zt (r₀ : ℤ)
  have hKU : Y.K ≤ Subgroup.normalizer (Y.Zt (r₀ : ℤ) : Set G) :=
    Y.K_le_normalizer_Zt (r₀ : ℤ)
  have h1 : Y.Zt (r₀ : ℤ) ⊔ Y.Q 0 = Y.edgeSylow 0 :=
    (gen_of_K_invariant Y H (j := 0) (by norm_num) hU2 hUr0 hKU hnotQ hUr).1
  exact (h1.trans Y.edgeSylow_zero).symm

theorem s52_step4 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) :
    Y.Z 1 = centerOf (Y.L 1) ∧ Nat.card (Y.Z 1) = 2 := by
  by_cases h0 : Y.Z 0 ≤ Y.Q 1
  · by_cases hQ : Nat.card (Y.Qs 1) ≤ 2
    · have h4 := Z_one_eq_center_of_small_Qs Y H h3 hQ
      exact ⟨h4, card_Z_one_of_eq_center Y H h3 h4⟩
    · obtain ⟨d, hdJ, hd3⟩ := exists_J_three Y H
      have h4le : 4 ≤ Nat.card (Y.Qs 1) := four_le_card_Qs_of_not_le Y H hQ
      have hlarge := (goldschmidt_small_apply Y H hdJ hd3).2.2.2 h4le
      have hEcard : Nat.card ↥⁅Y.Qs 1, Subgroup.zpowers d⁆ = 4 := hlarge.2.1
      by_cases hEZ : ⁅Y.Qs 1, Subgroup.zpowers d⁆ ≤ Y.Z 1
      · exact absurd (false_of_E_le Y H hZ h3 hdJ hd3 hEcard h0 hEZ) (by simp)
      · have hNbot : ⁅Y.Z 1, Subgroup.zpowers d⁆ = ⊥ := by
          rcases commutator_Z_one_eq_bot_or_eq_E Y H h3 hdJ hd3 hEcard with h | h
          · exact h
          · exact absurd (h ▸ commutator_Z_one_zpowers_le Y hdJ) hEZ
        have h4 := Z_one_eq_centerOf_L_one_of_commutator_eq_bot Y H h3 hdJ hd3 hEcard hNbot
        exact ⟨h4, card_Z_one_of_eq_center Y H h3 h4⟩
  · have h4 := Z_one_eq_center_of_not_le Y H h3 h0
    exact ⟨h4, card_Z_one_of_eq_center Y H h3 h4⟩

theorem Z_one_le (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) :
    Y.Z 1 ≤ Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) := by
  have h4 : Y.Z 1 = centerOf (Y.L 1) := (s52_step4 Y H hZ h3).1
  have hSL : Y.S ≤ Y.L 1 := Y.S_le_L_one
  have hZ1S : Y.Z 1 ≤ Subgroup.centralizer (Y.S : Set G) := by
    rw [h4]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_iff.mp hz.2 s (hSL hs)
  have hZ1Q0 : Y.Z 1 ≤ Y.Q 0 := by
    rw [h4]
    exact (Y.centerOf_L_le_Q_adj H.char 0).1
  have hZ1Z0 : Y.Z 1 ≤ Y.Z 0 := by
    have hZ1S' : Y.Z 1 ≤ Y.S :=
      hZ1Q0.trans (Y.Q_le_edgeSylow_left 0)
    have hle : Y.Z 1 ≤ centerOf Y.S := le_inf hZ1S' hZ1S
    exact hle.trans (center_S_le_Z Y H 0 (Or.inl rfl)).1
  have hZ1K : Y.Z 1 ≤ Subgroup.centralizer (Y.K : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  exact le_inf hZ1Z0 hZ1K


private theorem commutator_Z_zero_Zt_mem_of_le_Gi (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {r₀ : ℕ} (hZ : Y.Zt 0 ≠ ⊥) (he : Y.ZtExt 0 r₀ r₀) (hZ0r : Y.Z 0 ≤ Y.Gi (r₀ : ℤ)) :
    ∀ z ∈ Y.Z 0, ∀ e ∈ Y.Zt (r₀ : ℤ), ⁅z, e⁆ ∈ Y.Z 0 ⊓ Y.Z (r₀ : ℤ) := by
  have heven : Even r₀ := (s52_step1 Y H hZ he).2
  have hZtG0 : Y.Zt (r₀ : ℤ) ≤ Y.Gi 0 := he.Zt_le_Gi_zero heven
  intro z hz e hee
  constructor
  · have heG : e ∈ Y.Gi 0 := hZtG0 hee
    have hconj : e * z⁻¹ * e⁻¹ ∈ Y.Z 0 := by
      have h := mul_mem_conjSub (g := e) (H := Y.Z 0) (Subgroup.inv_mem _ hz)
      rwa [Y.Z_normal 0 e heG] at h
    have hmem : z * (e * z⁻¹ * e⁻¹) ∈ Y.Z 0 := Subgroup.mul_mem _ hz hconj
    simpa [commutatorElement_def, mul_assoc] using hmem
  · have hzG : z ∈ Y.Gi (r₀ : ℤ) := hZ0r hz
    have heZ : e ∈ Y.Z (r₀ : ℤ) := Zt_le_Z Y (r₀ : ℤ) hee
    have hconj : z * e * z⁻¹ ∈ Y.Z (r₀ : ℤ) := by
      have h := mul_mem_conjSub (g := z) (H := Y.Z (r₀ : ℤ)) heZ
      rwa [Y.Z_normal (r₀ : ℤ) z hzG] at h
    have hmem : (z * e * z⁻¹) * e⁻¹ ∈ Y.Z (r₀ : ℤ) :=
      Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ heZ)
    simpa [commutatorElement_def, mul_assoc] using hmem

private theorem commutator_Z_zero_S_le (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (he : Y.ZtExt 0 r₀ r₀)
    (hcomm : ∀ z ∈ Y.Z 0, ∀ e ∈ Y.Zt (r₀ : ℤ), ⁅z, e⁆ ∈ Y.Z 0 ⊓ Y.Z (r₀ : ℤ)) :
    ⁅Y.Z 0, Y.S⁆ ≤ Y.Z 0 ⊓ Y.Z (r₀ : ℤ) := by
  have heven : Even r₀ := (s52_step1 Y H hZ he).2
  have hZtG0 : Y.Zt (r₀ : ℤ) ≤ Y.Gi 0 := he.Zt_le_Gi_zero heven
  have hQ0N : Y.Zt (r₀ : ℤ) ≤ Subgroup.normalizer (Y.Q 0 : Set G) :=
    hZtG0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 0))
  have hS := S_eq_Zt_sup_Q_zero Y H hZ he
  rw [Subgroup.commutator_le]
  intro z hz s hs
  rw [hS, sup_comm] at hs
  obtain ⟨q, hq, e, hee, rfl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes (H := Y.Q 0)
      (K := Y.Zt (r₀ : ℤ)) hQ0N).mp hs
  have hqz : Commute z q := by
    have hc : z ∈ Subgroup.centralizer (Y.Q 0 : Set G) := (Y.Z_le_center 0 hz).2
    exact (Subgroup.mem_centralizer_iff.mp hc q hq).symm
  have hze : ⁅z, e⁆ ∈ Y.Z 0 ⊓ Y.Z (r₀ : ℤ) := hcomm z hz e hee
  have hqe : q * ⁅z, e⁆ * q⁻¹ = ⁅z, e⁆ := by
    have hc : (⁅z, e⁆ : G) ∈ Subgroup.centralizer (Y.Q 0 : Set G) :=
      (Y.Z_le_center 0 hze.1).2
    have hcq := Subgroup.mem_centralizer_iff.mp hc q hq
    rw [hcq, mul_assoc, mul_inv_cancel, mul_one]
  rw [commutatorElement_mul_right_eq_mul_conj, hqz.commutator_eq, one_mul, hqe]
  exact hze

private theorem commutator_inf_Z_S_eq_bot (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (he : Y.ZtExt 0 r₀ r₀) :
    ⁅Y.Z 0 ⊓ Y.Z (r₀ : ℤ), Y.S⁆ = ⊥ := by
  have heven : Even r₀ := (s52_step1 Y H hZ he).2
  have hZtG0 : Y.Zt (r₀ : ℤ) ≤ Y.Gi 0 := he.Zt_le_Gi_zero heven
  have hQ0N : Y.Zt (r₀ : ℤ) ≤ Subgroup.normalizer (Y.Q 0 : Set G) :=
    hZtG0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 0))
  have hS := S_eq_Zt_sup_Q_zero Y H hZ he
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  rw [hS, sup_comm] at hs
  obtain ⟨q, hq, e, hee, rfl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes (H := Y.Q 0)
      (K := Y.Zt (r₀ : ℤ)) hQ0N).mp hs
  have haZ0 : a ∈ Y.Z 0 := ha.1
  have haZr : a ∈ Y.Z (r₀ : ℤ) := ha.2
  have hqa : Commute a q := by
    have hc : a ∈ Subgroup.centralizer (Y.Q 0 : Set G) := (Y.Z_le_center 0 haZ0).2
    exact (Subgroup.mem_centralizer_iff.mp hc q hq).symm
  have hea : Commute a e :=
    Y.Z_commute (r₀ : ℤ) a haZr e (Zt_le_Z Y (r₀ : ℤ) hee)
  have hone : ⁅a, q * e⁆ = 1 := by
    rw [commutatorElement_mul_right_eq_mul_conj, hqa.commutator_eq, one_mul,
      hea.commutator_eq, mul_one, mul_inv_cancel]
  exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm

private theorem sq_mem_centralizer_S_of_mem_Z_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {r₀ : ℕ} (hZ : Y.Zt 0 ≠ ⊥) (he : Y.ZtExt 0 r₀ r₀)
    (hcomm : ∀ z ∈ Y.Z 0, ∀ e ∈ Y.Zt (r₀ : ℤ), ⁅z, e⁆ ∈ Y.Z 0 ⊓ Y.Z (r₀ : ℤ)) :
    ∀ y ∈ Y.Z 0, y ^ 2 ∈ Subgroup.centralizer (Y.S : Set G) := by
  have hWS : ⁅Y.Z 0, Y.S⁆ ≤ Y.Z 0 ⊓ Y.Z (r₀ : ℤ) :=
    commutator_Z_zero_S_le Y H hZ he hcomm
  have hSS : ⁅⁅Y.Z 0, Y.S⁆, Y.S⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono hWS le_rfl).trans
      (le_of_eq (commutator_inf_Z_S_eq_bot Y H hZ he)))
  have hcommS : ∀ z ∈ Y.Z 0, ∀ s ∈ Y.S, Commute s ⁅z, s⁆ := by
    intro z hz s hs
    have hmem : ⁅z, s⁆ ∈ ⁅Y.Z 0, Y.S⁆ := Subgroup.commutator_mem_commutator hz hs
    have hle : ⁅Y.Z 0, Y.S⁆ ≤ Subgroup.centralizer (Y.S : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hSS
    exact Subgroup.mem_centralizer_iff.mp (hle hmem) s hs
  have hsq : ∀ z ∈ Y.Z 0, ∀ s ∈ Y.S, ⁅z, s⁆ ^ 2 = 1 := by
    intro z hz s hs
    rw [(hcommS z hz s hs).commutatorElement_pow_right 2]
    have hq : Commute z (s ^ 2) := by
      have hc : z ∈ Subgroup.centralizer (Y.Q 0 : Set G) := (Y.Z_le_center 0 hz).2
      exact (Subgroup.mem_centralizer_iff.mp hc (s ^ 2) (Y.sq_mem_Q_of_relIndex
        (Y.edgeSylow_le_L 0) (Y.relIndex_Q_edgeSylow 0) s hs)).symm
    exact hq.commutator_eq
  have hsqz : ∀ z ∈ Y.Z 0, ∀ s ∈ Y.S, ⁅z ^ 2, s⁆ = 1 := by
    intro z hz s hs
    have hzS : ⁅z, s⁆ ∈ Y.Z 0 :=
      (hWS (Subgroup.commutator_mem_commutator hz hs)).1
    have hzc : Commute z ⁅z, s⁆ := Y.Z_commute 0 z hz ⁅z, s⁆ hzS
    rw [← hzc.commutatorElement_pow_left 2]
    exact hsq z hz s hs
  exact fun y hy => by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (commutatorElement_eq_one_iff_mul_comm.mp (hsqz y hy s hs)).symm

private theorem sq_mem_centerOf_L_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (he : Y.ZtExt 0 r₀ r₀)
    (hcomm : ∀ z ∈ Y.Z 0, ∀ e ∈ Y.Zt (r₀ : ℤ), ⁅z, e⁆ ∈ Y.Z 0 ⊓ Y.Z (r₀ : ℤ)) :
    ∀ z ∈ Y.Z 0, z ^ 2 ∈ centerOf (Y.L 0) := by
  have hZs := sq_mem_centralizer_S_of_mem_Z_zero Y H hZ he hcomm
  obtain ⟨g, hgL, hg1⟩ := (Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).trans
    (Y.vert (-1)) (Y.vert 1) (by simpa using (Y.adj (-1)).symm) (by simpa using Y.adj 0)
  have hgGi : g ∈ Y.Gi 0 := Y.L_le_Gi 0 hgL
  have hgfix : g • Y.vert 0 = Y.vert 0 := MulAction.mem_stabilizer_iff.mp hgGi
  have h0 : conjSub g (Y.Gi 0) = Y.Gi 0 := by
    rw [← stabilizer_smul_eq_conjSub, hgfix]
  have hconjGm : conjSub g (Y.Gi (-1)) = Y.Gi 1 := by
    rw [← stabilizer_smul_eq_conjSub, hg1]
  have hconjS : conjSub g (Y.edgeSylow (-1)) = Y.S := by
    have hGm : Y.edgeSylow (-1) = pCoreOf 2 (Y.Gi (-1) ⊓ Y.Gi 0) := by
      unfold Setup.edgeSylow
      rw [show (-1 : ℤ) + 1 = 0 by ring]
    rw [hGm, ← pCoreOf_conjSub, conjSub_inf, hconjGm, h0, inf_comm]
  have hGm : conjSub g⁻¹ (Y.S) = Y.edgeSylow (-1) := by
    rw [← hconjS, conjSub_conjSub_inv]
  have hLS : Y.L 0 = conjSub g⁻¹ (Y.S) ⊔ Y.S := by
    rw [show Y.L 0 = Y.edgeSylow (-1) ⊔ Y.edgeSylow 0 by
      simpa using (Y.edgeSylow_sup_edgeSylow 0).symm, Y.edgeSylow_zero, ← hGm]
  intro z hz
  have hz2Z : z ^ 2 ∈ Y.Z 0 := (Y.Z 0).pow_mem hz 2
  have hz2L : z ^ 2 ∈ Y.L 0 :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (Y.Gi 0)) (Y.Q_le_Gi 0) (Y.Z_le_Q 0 hz2Z)
  refine Subgroup.mem_inf.mpr ⟨hz2L, ?_⟩
  have hcent : Y.L 0 ≤ Subgroup.centralizer ({z ^ 2} : Set G) := by
    rw [hLS]
    apply sup_le
    · intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hgl : g * l * g⁻¹ ∈ Y.S := by
        simpa using mem_conjSub.mp hl
      have hz' : g * z * g⁻¹ ∈ Y.Z 0 := by
        have hmem : g * z * g⁻¹ ∈ conjSub g (Y.Z 0) :=
          mem_conjSub.mpr (by
            have heq : g⁻¹ * (g * z * g⁻¹) * g = z := by group
            rwa [heq])
        rwa [Y.Z_normal 0 g hgGi] at hmem
      have h2 := hZs (g * z * g⁻¹) hz' (g * l * g⁻¹) hgl
      have hz2 : (g * z * g⁻¹) ^ 2 = g * z ^ 2 * g⁻¹ := (conj_pow (i := 2))
      rw [hz2] at h2
      have h3 : g * (l * z ^ 2) * g⁻¹ = g * (z ^ 2 * l) * g⁻¹ := by
        calc g * (l * z ^ 2) * g⁻¹ = (g * l * g⁻¹) * (g * z ^ 2 * g⁻¹) := by group
          _ = (g * z ^ 2 * g⁻¹) * (g * l * g⁻¹) := h2
          _ = g * (z ^ 2 * l) * g⁻¹ := by group
      have h4 : l * z ^ 2 = z ^ 2 * l := by
        have h5 := congrArg (fun x => g⁻¹ * x * g) h3
        simpa [mul_assoc] using h5
      exact h4
    · intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (hZs z hz) l hl
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have := hcent hl
  rwa [Subgroup.mem_centralizer_singleton_iff] at this

private theorem K_le_normalizer_center_S (Y : Setup Γ G) :
    Y.K ≤ Subgroup.normalizer (centerOf (Y.S) : Set G) :=
  (Y.K_le_inf.trans
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 0 ⊓ Y.Gi 1))).trans
    (CFSG.Quasithin.normalizer_le_normalizer_centerOf Y.S)

private theorem Z_zero_eq_iSup_center_S (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Y.Z 0 = (⨆ l ∈ Y.L 0, (Y.Z 0 ⊓ centerOf (Y.S : Subgroup G)).map
      (MulAut.conj l).toMonoidHom) ⊔ centerOf (Y.L 0) := by
  haveI : Finite ↥(Y.Gi 0) := Y.hyp.finite_stab (Y.vert 0)
  have hSsyl : IsSylowTwoOf Y.S (Y.Gi 0) := isSylowTwoOf_S_Gi_zero Y
  have hZSZ : centerOf (Y.S) ≤ Y.Z 0 :=
    (center_S_le_Z Y H 0 (Or.inl rfl)).1
  have hG0 : Y.Gi 0 = Y.L 0 ⊔ Y.K := Y.Gi_eq_L_sup_K 0
  have hKN : Y.K ≤ Subgroup.normalizer (Y.L 0 : Set G) :=
    Y.K_le_Gi 0 |>.trans (CFSG.Quasithin.le_normalizer_oTwoPrime (Y.Gi 0))
  have hKZ : Y.K ≤ Subgroup.normalizer (centerOf (Y.S) : Set G) := K_le_normalizer_center_S Y
  apply le_antisymm
  · rw [Setup.Z]
    refine iSup_le fun P => iSup_le fun hP => ?_
    intro z hz
    obtain ⟨hzP, -⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨g, hgG0, hgP⟩ := CFSG.GroupTheory.exists_eq_conjSub_of_isSylowTwoOf hSsyl hP
    have hconjZ : centerOf (conjSub g (Y.S)) = conjSub g (centerOf (Y.S)) :=
      centerOf_conjSub g Y.S
    have hzZ : z ∈ conjSub g (centerOf (Y.S)) := by
      rw [← hconjZ, ← hgP]
      exact hzP
    obtain ⟨w, hwS, hwz⟩ := Subgroup.mem_map.mp hzZ
    obtain ⟨l, hl, k, hk, hlk⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes (H := Y.L 0)
        (K := Y.K) hKN).mp (hG0 ▸ hgG0)
    have hkw : (MulAut.conj k) w ∈ Y.Z 0 ⊓ centerOf (Y.S) := by
      have hkw' : (MulAut.conj k) w ∈ centerOf (Y.S) :=
        (Subgroup.mem_normalizer_iff.mp (hKZ hk) w).mp hwS
      exact Subgroup.mem_inf.mpr ⟨hZSZ hkw', hkw'⟩
    have hz_eq : z = (MulAut.conj l) ((MulAut.conj k) w) := by
      rw [← hwz, hlk, map_mul]
      rfl
    rw [hz_eq]
    exact Subgroup.mem_sup_left
      ((le_iSup₂_of_le (f := fun l (_ : l ∈ Y.L 0) =>
          (Y.Z 0 ⊓ centerOf (Y.S)).map (MulAut.conj l).toMonoidHom)
        (a := (Y.Z 0 ⊓ centerOf (Y.S)).map (MulAut.conj l).toMonoidHom) l hl le_rfl)
        (Subgroup.mem_map_of_mem _ hkw))
  · refine sup_le ?_ (Y.centerOf_L_le_Z H.char 0)
    refine iSup_le fun l => iSup_le fun hl => ?_
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    have hmem : (MulAut.conj l) w ∈ conjSub l (Y.Z 0) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.mp hw).1
    rwa [Y.Z_normal 0 l (Y.L_le_Gi 0 hl)] at hmem

private theorem Z_zero_eq_iSup_centralizer_S (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Y.Z 0 = (⨆ l ∈ Y.L 0, (Y.Z 0 ⊓ Subgroup.centralizer (Y.S : Set G)).map
      (MulAut.conj l).toMonoidHom) ⊔ centerOf (Y.L 0) := by
  haveI : Finite ↥(Y.Gi 0) := Y.hyp.finite_stab (Y.vert 0)
  have hGiZ : Y.Gi 0 ≤ Subgroup.normalizer (Y.Z 0 : Set G) := Y.Gi_le_normalizer_Z 0
  apply le_antisymm
  · have h1 : (⨆ x ∈ Y.L 0, (Y.Z 0 ⊓ centerOf (Y.S)).map (MulAut.conj x).toMonoidHom) ≤
        (⨆ x ∈ Y.L 0, (Y.Z 0 ⊓ Subgroup.centralizer (Y.S : Set G)).map
          (MulAut.conj x).toMonoidHom) :=
      iSup₂_le (f := fun x (_ : x ∈ Y.L 0) =>
          (Y.Z 0 ⊓ centerOf (Y.S)).map (MulAut.conj x).toMonoidHom)
        (fun x hx =>
          (Subgroup.map_mono (inf_le_inf le_rfl inf_le_right)).trans (le_iSup₂_of_le x hx le_rfl))
    exact le_trans (Z_zero_eq_iSup_center_S Y H).le (sup_le (h1.trans le_sup_left) le_sup_right)
  · refine sup_le ?_ (Y.centerOf_L_le_Z H.char 0)
    refine iSup₂_le (f := fun x (_ : x ∈ Y.L 0) =>
      (Y.Z 0 ⊓ Subgroup.centralizer (Y.S : Set G)).map (MulAut.conj x).toMonoidHom) ?_
    intro x hx z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    have hwZ : w ∈ Y.Z 0 := (Subgroup.mem_inf.mp hw).1
    have h := (Subgroup.mem_normalizer_iff.mp (hGiZ (Y.L_le_Gi 0 hx)) w).mp hwZ
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h

private theorem fixFree_of_higmanQuad (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (he : Y.ZtExt 0 r₀ r₀) (hHQ : HigmanQuad n₀)
    (hcomm : ∀ z ∈ Y.Z 0, ∀ e ∈ Y.Zt (r₀ : ℤ), ⁅z, e⁆ ∈ Y.Z 0 ⊓ Y.Z (r₀ : ℤ))
    {k : G} (hkK : k ∈ Y.K) (hk1 : k ≠ 1) : FixFree (centerOf (Y.L 0)) (Y.Z 0) k := by
  haveI : Finite ↥(Y.L 0) := finite_of_le_stabilizer Y.hyp (Y.L_le_Gi 0)
  have hGiZ : Y.Gi 0 ≤ Subgroup.normalizer (Y.Z 0 : Set G) := Y.Gi_le_normalizer_Z 0
  have hpc : pCoreOf 2 (Y.L 0) = Y.Q 0 := (Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).pCoreOf_eq
  refine hHQ.fixFree (isL2Quot_L_zero Y H)
    (by rw [← Y.edgeSylow_zero]; exact Y.isSylowTwoOf_edgeSylow_L 0)
    ⟨Y.centerOf_L_le_Z H.char 0, Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [Commute.commutator_eq (Y.Z_commute 0 a ha b hb)]
      exact one_mem _,
      sq_mem_centerOf_L_zero Y H hZ he hcomm⟩
    (by rw [hpc]; exact Y.Z_le_Q 0) ((Y.L_le_Gi 0).trans hGiZ)
    (le_normalizer_centerOf_self (Y.L 0)) ?_
    (fun v hv hvl => Y.mem_centerOf_L_of_commutator_mem
      (Y.L_eq_commutator_sup_Q 0 H.two_le (isL2Quot_L_zero Y H)) (Y.Z_le_center 0 hv) hvl) ?_
    (Z_zero_eq_iSup_centralizer_S Y H) k (Y.K_le_L_zero H hkK)
    (Y.odd_card_K.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y.K hkK)) hk1
  · intro q hq v hv
    rw [hpc] at hq
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp (Y.Z_le_center 0 hv).2 q hq)]
    exact one_mem _
  · intro v hv a ha b hb
    have h := Subgroup.commutator_mem_commutator
      (commutator_Z_zero_S_le Y H hZ he hcomm (Subgroup.commutator_mem_commutator hv ha)) hb
    rw [commutator_inf_Z_S_eq_bot Y H hZ he, Subgroup.mem_bot] at h
    rw [h]
    exact one_mem _

theorem false_of_comm_Zt_le (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (he : Y.ZtExt 0 r₀ r₀)
    (hHQ : HigmanQuad n₀)
    (hcomm : ∀ z ∈ Y.Z 0, ∀ e ∈ Y.Zt (r₀ : ℤ), ⁅z, e⁆ ∈ Y.Z 0 ⊓ Y.Z (r₀ : ℤ)) : False := by
  have h4 : Y.Z 1 = centerOf (Y.L 1) := (s52_step4 Y H hZ h3).1
  have hZ1le : Y.Z 1 ≤ Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) := Z_one_le Y H hZ h3
  obtain ⟨k, hkK, hk1⟩ := (Subgroup.bot_or_exists_ne_one Y.K).resolve_left (Y.K_ne_bot H)
  have hff := fixFree_of_higmanQuad Y H hZ he hHQ hcomm hkK hk1
  have hZ1Z : Y.Z 1 ≤ centerOf (Y.L 0) := by
    intro z hz
    have hzZ : z ∈ Y.Z 0 := (hZ1le hz).1
    have hzK : z ∈ Subgroup.centralizer (Y.K : Set G) := (hZ1le hz).2
    have hzk : ⁅z, k⁆ = 1 := Subgroup.mem_centralizer_iff_commutator_eq_one'.mp hzK k hkK
    exact hff z hzZ (by rw [hzk]; exact (centerOf (Y.L 0)).one_mem)
  have hbot : Y.Z 1 = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : z ∈ centerOf (Y.L 0) ⊓ centerOf (Y.L 1) := by
      refine Subgroup.mem_inf.mpr ⟨hZ1Z hz, ?_⟩
      rw [← h4]; exact hz
    have hinf : centerOf (Y.L 0) ⊓ centerOf (Y.L 1) = ⊥ := by
      simpa using Y.centerOf_L_inf_succ H.char 0
    rw [hinf] at h1
    exact h1
  exact Y.Z_ne_bot_of 1 (Y.Q_ne_bot H.char 1) hbot

theorem s52_step5 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (he : Y.ZtExt 0 r₀ r₀)
    (hHQ : HigmanQuad n₀) : ¬ Y.Z 0 ≤ Y.Gi (r₀ : ℤ) := fun hZ0r =>
  false_of_comm_Zt_le Y H hZ h3 he hHQ
    (commutator_Z_zero_Zt_mem_of_le_Gi Y H hZ he hZ0r)

private theorem commutator_Zt_Zt_K_eq_bot (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (hr : Y.IsMaxRegLen r)
    (he : Y.ZtExt 0 r₀ r₀) (h2 : Y.Step2Conclusion s r r₀)
    (h5 : ¬ Y.Z 0 ≤ Y.Gi (r₀ : ℤ) ∧ ¬ Y.Z 0 ≤ Y.Gi (-(r₀ : ℤ)))
    (hX_t0 : ⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆ ≤ Y.Zt 0)
    (hX_tr : ⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆ ≤ Y.Zt (r₀ : ℤ)) :
    ⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆ = ⊥ := by
  have heven : Even r₀ := (s52_step1 Y H hZ (l := r₀) he).2
  have hXQ : ⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆ ≤ Y.Q 0 :=
    hX_t0.trans ((Zt_le_Z Y 0).trans (Y.Z_le_Q 0))
  have hX2 : IsPGroup 2 ↥⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆ :=
    (pCoreOf_isPGroup' (Y.Gi 0)).to_le hXQ
  have hXarc := le_arcStab_of_le_Zt Y (X := ⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆) he heven hX_t0 hX_tr
  by_contra hXne
  have h3r : 3 * r₀ ≤ r := by
    by_contra h
    have hlt : r < 3 * r₀ := by omega
    have hGT : Y.arcStab (-(r₀ : ℤ)) (-(r₀ : ℤ) + ((3 * r₀ : ℕ) : ℤ)) = Y.GT :=
      hr.2 (-(r₀ : ℤ)) (3 * r₀) hlt
    have hXGT : ⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆ ≤ Y.GT := hGT ▸ hXarc
    have hoddX : Odd (Nat.card ↥⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆) :=
      H.odd_GT.of_dvd_nat (Subgroup.card_dvd_of_le hXGT)
    exact hXne (by simpa using inf_eq_bot_of_odd_of_isPGroup hoddX hX2)
  have h2le : r ≤ 2 * r₀ + 2 := by
    rcases h2 with h | h | h
    · omega
    · omega
    · omega
  have hr₀2 : r₀ = 2 := by
    have hpos : 1 ≤ r₀ := he.one_le.1
    have hle : r₀ ≤ 2 := by omega
    obtain ⟨k, hk⟩ := heven
    omega
  have hQ0Gi1 : Y.Q 0 ≤ Y.Gi 1 :=
    (Y.Q_le_Gi_adj 0).trans inf_le_right
  have hQ0GiNeg1 : Y.Q 0 ≤ Y.Gi (-1) :=
    by simpa using (Y.Q_le_Gi_adj 0).trans inf_le_left
  have hb : Y.HasB 0 1 := by
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      have hj1 : j ≤ 1 := by
        have h := Int.le_natAbs (a := j)
        omega
      have hj2 : -1 ≤ j := by
        have h := Int.le_natAbs (a := -j)
        rw [Int.natAbs_neg] at h
        omega
      have hcases : j = -1 ∨ j = 0 ∨ j = 1 := by omega
      rcases hcases with rfl | rfl | rfl
      · exact (Y.Z_le_Q 0).trans (by simpa using hQ0GiNeg1)
      · simpa using Y.Z_le_Gi 0
      · exact (Y.Z_le_Q 0).trans (by simpa using hQ0Gi1)
    · simpa [hr₀2] using h5.1
    · simpa [hr₀2] using h5.2
  have h4 : Y.Z 1 = centerOf (Y.L 1) := (s52_step4 Y H hZ h3).1
  have hZinf : Y.Z 0 ⊓ Y.Z 2 = Y.Z 1 := Z_inf_Z_eq Y H h4 hb
  have hX_Z1 : ⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆ ≤ Y.Z 1 := by
    rw [← hZinf]
    refine le_inf (hX_t0.trans (Zt_le_Z Y 0)) ?_
    simpa [hr₀2] using hX_tr.trans (Zt_le_Z Y (r₀ : ℤ))
  have hZ1K : Y.Z 1 ≤ Subgroup.centralizer (Y.K : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  have hX_CK : ⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆ ≤ Subgroup.centralizer (Y.K : Set G) :=
    hX_Z1.trans hZ1K
  have hZt0K : Y.Zt 0 ⊓ Subgroup.centralizer (Y.K : Set G) = ⊥ := (Zt_eq Y H 0).2.1
  have hbot : ⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆ ≤ (⊥ : Subgroup G) := by
    rw [← hZt0K]
    exact le_inf hX_t0 hX_CK
  exact hXne (le_bot_iff.mp hbot)

theorem s52_step6 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (hr : Y.IsMaxRegLen r)
    (he : Y.ZtExt 0 r₀ r₀) (h2 : Y.Step2Conclusion s r r₀)
    (h5 : ¬ Y.Z 0 ≤ Y.Gi (r₀ : ℤ) ∧ ¬ Y.Z 0 ≤ Y.Gi (-(r₀ : ℤ))) :
    ⁅Y.Zt 0, Y.Zt r₀⁆ ≤ Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) := by
  have heven : Even r₀ := (s52_step1 Y H hZ (l := r₀) he).2
  have hZtr0G : Y.Zt (r₀ : ℤ) ≤ Y.Gi 0 := he.Zt_le_Gi_zero heven
  have hR_Z0 : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Y.Z 0 :=
    (Subgroup.commutator_mono (Zt_le_Z Y 0) le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp fun g hg =>
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Y.Z_normal 0 g (hZtr0G hg)))
  have hR_Zr : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Y.Z (r₀ : ℤ) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    have haG : a ∈ Y.Gi (r₀ : ℤ) := by
      have h := he.1 (r₀ : ℤ) (by linarith) (le_refl _) ha
      simpa using h
    have hbZ : b ∈ Y.Z (r₀ : ℤ) := Zt_le_Z Y (r₀ : ℤ) hb
    have hconj : a * b * a⁻¹ ∈ Y.Z (r₀ : ℤ) := by
      have h := mul_mem_conjSub (g := a) (H := Y.Z (r₀ : ℤ)) hbZ
      rwa [Y.Z_normal (r₀ : ℤ) a haG] at h
    have hmem : (a * b * a⁻¹) * b⁻¹ ∈ Y.Z (r₀ : ℤ) :=
      Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hbZ)
    simpa only [mul_assoc] using hmem
  have hX_t0 : ⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆ ≤ Y.Zt 0 := by
    have h := Subgroup.commutator_mono hR_Z0 (le_refl Y.K)
    simpa [Setup.Zt] using h
  have hX_tr : ⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆ ≤ Y.Zt (r₀ : ℤ) := by
    have h := Subgroup.commutator_mono hR_Zr (le_refl Y.K)
    simpa [Setup.Zt] using h
  have hXQ : ⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆ ≤ Y.Q 0 :=
    hX_t0.trans ((Zt_le_Z Y 0).trans (Y.Z_le_Q 0))
  have hX2 : IsPGroup 2 ↥⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆ :=
    (pCoreOf_isPGroup' (Y.Gi 0)).to_le hXQ
  haveI hXfin : Finite ↥⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆ :=
    finite_of_le_stabilizer Y.hyp (H := ⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆)
      (hXQ.trans (Y.Q_le_Gi 0))
  have hXarc := le_arcStab_of_le_Zt Y (X := ⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆) he heven hX_t0 hX_tr
  have hX_t0 : ⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆ ≤ Y.Zt 0 := by
    have h := Subgroup.commutator_mono hR_Z0 (le_refl Y.K)
    simpa [Setup.Zt] using h
  have hX_tr : ⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆ ≤ Y.Zt (r₀ : ℤ) := by
    have h := Subgroup.commutator_mono hR_Zr (le_refl Y.K)
    simpa [Setup.Zt] using h
  have hXbot := commutator_Zt_Zt_K_eq_bot Y H hZ h3 hr he h2 h5 hX_t0 hX_tr
  refine le_inf hR_Z0 ?_
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  simpa only [Setup.Zt] using hXbot

end Setup

end CFSG.Quasithin.St84
