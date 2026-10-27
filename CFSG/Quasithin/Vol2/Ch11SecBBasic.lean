module

public import CFSG.Quasithin.Vol2.Ch11StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecABasicV
public import CFSG.Quasithin.Background.E3Prop
public import CFSG.Quasithin.Background.B2FactorizationR2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative Pointwise

section General

variable {G : Type} [Group G]

theorem inf_centralizer_ne_bot [Finite G] {P W : Subgroup G} (hP : IsPGroup 2 P)
    (hWP : W ≤ P) (hnorm : P ≤ Subgroup.normalizer (W : Set G)) (hW : W ≠ ⊥) :
    W ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnormal : (W.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hne : W.subgroupOf P ≠ ⊥ := by
    intro h
    apply hW
    rw [← Subgroup.map_subgroupOf_eq_of_le hWP, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ W ⊓ Subgroup.centralizer (P : Set G) := ⟨hy.1, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

theorem isMulCommutative_of_le {K V : Subgroup G} (hKV : K ≤ V) (hV : IsMulCommutative ↥V) :
    IsMulCommutative ↥K :=
  IsMulCommutative.of_comm fun a b => Subtype.ext (by
    have := mul_comm' (⟨a, hKV a.2⟩ : ↥V) ⟨b, hKV b.2⟩
    show (a : G) * b = b * a
    exact congrArg Subtype.val this)

theorem le_normalizer_wClos [Finite G] {T H V : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hTH : T ≤ H) (hW : E3.wClos V 0 T ≤ pCoreOf 2 H) :
    H ≤ Subgroup.normalizer (E3.wClos V 0 T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H).trans
    (E3.e3_15_normalizer (isSylowTwoOf_of_quasithinIsSylowTwo hT hTH)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 H) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hW)

theorem autI_mem_aSet [Finite G] {V W H : Subgroup G} (hV : IsElemAbelian 2 V)
    (hW : IsElemAbelian 2 W) {g : G} (hAH : conjSubgroup V g ≤ H)
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hAC : ¬ conjSubgroup V g ≤ Subgroup.centralizer (W : Set G)) :
    autI hW (conjSubgroup V g) ∈ E3.aSet (E3.sParam hV) (autI hW H) := by
  have hAN : conjSubgroup V g ≤ Subgroup.normalizer (W : Set G) := hAH.trans hHW
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  refine ⟨autI_mono hW hAH, (autI_eq_bot_iff hW hAN).not.2 hAC, isElemAbelian2_autI hW hVg hAN,
    fun B hB hm => ?_⟩
  rw [E3.mQuot_autI_preI hW hAN hB] at hm
  have hB'A : preI hW (conjSubgroup V g) hAN B ≤ conjSubgroup V g := preI_le hW
  have hs : E3.sParam hVg = E3.sParam hV := E3.sParam_conj hV g hVg
  have h6 := E3.e3_6 hVg (A := conjSubgroup V g) (B := preI hW (conjSubgroup V g) hAN B)
    (E := W) hB'A le_rfl (by rw [hs]; exact hm) (B2F.isPGroup_of_isElemAbelian hW)
  ext w
  have e1 : w ∈ fixV B ↔
      w.val ∈ Subgroup.centralizer (preI hW (conjSubgroup V g) hAN B : Set G) := by
    conv_lhs => rw [← autI_preI hW hB (hA := hAN)]
    exact mem_fixV_autI hW (hB'A.trans hAN) w
  rw [e1, mem_fixV_autI hW hAN w]
  constructor
  · intro hc
    have h1 : w.val ∈ W ⊓ Subgroup.centralizer
        (preI hW (conjSubgroup V g) hAN B : Set G) := ⟨IntMod.val_mem w, hc⟩
    rw [← h6.1] at h1
    exact h1.2
  · intro hc
    have h1 : w.val ∈ W ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) :=
      ⟨IntMod.val_mem w, hc⟩
    rw [h6.1] at h1
    exact h1.2

end General

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem normalizer_inf_le (h1103 : Stmt11_0_3) (hyp : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) :
    Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G) ≤
      Subgroup.normalizer (fsuV T I : Set G) := by
  intro g hg
  by_contra hgV
  have hbot := (h1103 G T L I n hyp).2.2.2.1.2 g (Subgroup.mem_inf.1 hg).1 hgV
  apply SecA.IsVi.ne_bot hyp hV₁ le_rfl
  rw [eq_bot_iff, ← hbot]
  intro x hx
  refine Subgroup.mem_inf.2 ⟨SecA.IsVi.le_fsuV hV₁ hx, mem_conjSubgroup_iff.2 ?_⟩
  exact SecA.IsVi.le_fsuV hV₁
    (((Subgroup.mem_normalizer_iff.1 (Subgroup.mem_inf.1 hg).2) x).1 hx)

theorem isMulCommutative_conjClosure (h1103 : Stmt11_0_3) (hyp : Hyp11 G T L I n)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hle : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    IsMulCommutative ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) := by
  refine isMulCommutative_of_le (V := fsuV T I) ?_ (SecA.isElemAbelian_fsuV hyp).1
  refine conjClosure_le fun h hh z hz => ?_
  have hN := normalizer_inf_le h1103 hyp hV₁ ⟨hle hh, hh⟩
  exact ((Subgroup.mem_normalizer_iff.1 hN) z).1 hz

theorem inf_centralizer_eq_bot (h331 : Stmt3_3_1) (hyp : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁)
    (hC : ¬ Subgroup.centralizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  by_contra hne
  set W := fsuV T I ⊓ Subgroup.centralizer (L : Set G) with hW
  have hWT : W ≤ T := inf_le_left.trans (SecA.fsuV_le_T hyp)
  have hTW : T ≤ Subgroup.normalizer (W : Set G) := by
    intro t ht
    have h1 := SecA.T_le_normalizer_fsuV T I ht
    have h2 : t ∈ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
      B2F.le_normalizer_centralizer hyp.normal ht
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro x
    simp only [hW, Subgroup.mem_inf]
    rw [h1 x, h2 x]
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (inf_centralizer_ne_bot hyp.fsu.sylow.1 hWT hTW hne)
  have hxW : (x : G) ∈ W := (Subgroup.mem_inf.1 x.2).1
  have hxT : (x : G) ∈ Subgroup.centralizer (T : Set G) := (Subgroup.mem_inf.1 x.2).2
  have hxL : (x : G) ∈ Subgroup.centralizer (L : Set G) := (Subgroup.mem_inf.1 hxW).2
  have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hP : IsPGroup 2 (Subgroup.zpowers (x : G)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime
      ((SecA.isElemAbelian_fsuV hyp).2 _ (Subgroup.mem_inf.1 hxW).1) hx1', pow_one]
  have hP1 : Subgroup.zpowers (x : G) ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]; exact hx1'
  have hCx : Subgroup.centralizer ({(x : G)} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers (x : G) : Set G) := by
    rw [show Subgroup.centralizer ({(x : G)} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers (x : G) : Set G) by
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]]
    exact Subgroup.centralizer_le_normalizer _
  have hLT : L ⊔ T ≤ Subgroup.normalizer (Subgroup.zpowers (x : G) : Set G) := by
    refine (sup_le ?_ ?_).trans hCx
    · intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hxL) l hl
    · intro t ht
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hxT) t ht
  apply hC
  refine le_trans ?_ (SecA.normalizer_le_of_isPGroup h331 hyp hP hP1 hLT)
  refine le_trans ?_ hCx
  exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 (SecA.IsVi.cV_le hV₁ hxW))

theorem conjClosure_normalizer_le (h1103 : Stmt11_0_3) (h1123 : Stmt11_2_3)
    (hyp : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (h3 : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ≤
      conjClosure (fsuV T I) (Subgroup.centralizer (V₁ : Set G)) := by
  have hfac := (h1123 G T L I n V₁ hyp hV₁).1 h3
  refine conjClosure_le fun h hh z hz => ?_
  have hh' : h ∈ (Subgroup.centralizer (V₁ : Set G) : Set G) *
      ((Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) :
        Set G) := by
    rw [← hfac]; exact hh
  obtain ⟨c, hc, m, hm, rfl⟩ := Set.mem_mul.1 hh'
  have hmV := normalizer_inf_le h1103 hyp hV₁ hm
  have hz' : m * z * m⁻¹ ∈ fsuV T I := ((Subgroup.mem_normalizer_iff.1 hmV) z).1 hz
  have e : c * m * z * (c * m)⁻¹ = c * (m * z * m⁻¹) * c⁻¹ := by group
  rw [e]
  exact mem_conjClosure hc hz'

theorem sParam_le_nParam (hyp : Hyp11 G T L I n) {V₁ H : Subgroup G}
    (h31 : Hyp11_3_1 T L I n V₁ H) (hW : ¬ E3.wClos (fsuV T I) 0 T ≤ pCoreOf 2 H)
    (hV : IsElemAbelian 2 (fsuV T I)) : (E3.sParam hV : ℕ∞) ≤ E1.nParam H := by
  obtain ⟨S, hS⟩ : ∃ S : Sylow 2 G, (S : Subgroup G) = T :=
    ⟨hyp.fsu.sylow.1.toSylow hyp.fsu.sylow.2, rfl⟩
  subst hS
  exact E3.e3_20 hV h31.hstar h31.moves hW

theorem isElemAbelian_VZ (hyp : Hyp11 G T L I n) {V₁ H : Subgroup G}
    (h31 : Hyp11_3_1 T L I n V₁ H) : IsElemAbelian 2 (VZ T H) :=
  (conjClosure_isTwoReducedIn_of_charTwo
    (isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow h31.hstar.1.1)
    (charTwo_of_inH hyp.fsu.qtke.2.1 (hyp.fsu.sylow.1.toSylow hyp.fsu.sylow.2) h31.hstar.1)
    le_rfl).2.1

end CFSG.Quasithin.Vol2.Ch11.SecB
