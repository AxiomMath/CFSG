module

public import CFSG.Quasithin.EmptyFaithful.S151S4D
public import CFSG.Quasithin.EmptyFaithful.SBd8Psl2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245BaumannSingle
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLAInv

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem isPSL_of_isLin2Type1521 {L : Subgroup G} {n : ℕ} (hn : 2 ≤ n) (h : IsLin2Type L n) :
    IsPSL 2 2 n (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨F, hF, hfin, hcard, α, hαs, hαk, -⟩ := h
  have e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  exact SBd8.Psl2.isPSL_of_statedSL hn (by rw [Nat.card_eq_fintype_card]; exact hcard)
    (e.trans (specialLinearGroupEquivStatedSL 2 F))

section Parabolic

variable [Finite G]

theorem isMinimalParabolic_l2 {L S : Subgroup G} {n : ℕ} (hn : 2 ≤ n) (hLn : IsLin2Type L n)
    (hS2 : IsPGroup 2 ↥S) (hSN : S ≤ Subgroup.normalizer (L : Set G))
    (hsyl : IsSylowTwoOf (S ⊓ L) L) : IsMinimalParabolic S (L ⊔ S) := by
  obtain ⟨Bor, hBorL, hBBor, hBorne, hmax, hnn⟩ :=
    S151S4.l2_rank_one hn (isPSL_of_isLin2Type1521 hn hLn) hsyl
  have hSH : IsSylowTwoOf S (L ⊔ S) := S151S4.sylow_sup_of_normalizes hSN hS2 hsyl
  have hSB : ∀ s ∈ S, s ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    fun s hs => zb_mem_normalizer_inf (Subgroup.le_normalizer hs) (hSN hs)
  have hconj : ∀ s ∈ S, ∀ x ∈ Bor, s * x * s⁻¹ ∈ Bor := by
    intro s hs
    have hKL : B6.conjSub s Bor ≤ L := by
      intro x hx
      have h1 : s⁻¹ * x * s ∈ Bor := B6.mem_conjSub.mp hx
      have h2 : s * (s⁻¹ * x * s) * s⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hSN hs) (s⁻¹ * x * s)).mp (hBorL h1)
      simpa [mul_assoc] using h2
    have hBK : S ⊓ L ≤ B6.conjSub s Bor := by
      intro b hb
      refine B6.mem_conjSub.mpr (hBBor ?_)
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem (hSB s hs)) b).mp hb
      simpa using this
    rcases hmax _ hBK hKL with h | h
    · intro x hx
      have : s * x * s⁻¹ ∈ B6.conjSub s Bor := B6.mem_conjSub.mpr (by simpa [mul_assoc] using hx)
      exact h this
    · exfalso
      apply hBorne
      refine le_antisymm hBorL (fun y hy => ?_)
      have hy' : s * y * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hSN hs) y).mp hy
      have : s * y * s⁻¹ ∈ B6.conjSub s Bor := h ▸ hy'
      simpa [mul_assoc] using B6.mem_conjSub.mp this
  have hSBor : S ≤ Subgroup.normalizer (Bor : Set G) := fun s hs =>
    B6.mem_normalizer_of_forall_mem (hconj s hs) (fun x hx => by
      simpa using hconj s⁻¹ (S.inv_mem hs) x hx)
  have hX_le : Bor ⊔ S ≤ L ⊔ S := sup_le (hBorL.trans le_sup_left) le_sup_right
  have hXne : Bor ⊔ S ≠ L ⊔ S := by
    intro hXeq
    apply hBorne
    refine le_antisymm hBorL (fun l hl => ?_)
    have hl' : l ∈ Bor ⊔ S := hXeq ▸ Subgroup.mem_sup_left hl
    obtain ⟨b, hb, s, hs, hbs⟩ := zb_mem_sup hSBor hl'
    have hsL : s ∈ L := by
      have : s = b⁻¹ * l := by rw [hbs]; group
      rw [this]
      exact L.mul_mem (L.inv_mem (hBorL hb)) hl
    have hsBor : s ∈ Bor := hBBor ⟨hs, hsL⟩
    rw [hbs]
    exact Bor.mul_mem hb hsBor
  have hXH : Bor ⊔ S < L ⊔ S := lt_of_le_of_ne hX_le hXne
  have hmaxX : ∀ Y : Subgroup G, S ≤ Y → Y < L ⊔ S → Y ≤ Bor ⊔ S := by
    intro Y hSY hYH
    have hY1 : Y ⊓ L ≤ Bor := by
      rcases hmax (Y ⊓ L) (le_inf (inf_le_left.trans hSY) inf_le_right) inf_le_right with h | h
      · exact h
      · exfalso
        have hLY : L ≤ Y := by
          intro x hx
          have hx' : x ∈ Y ⊓ L := by
            rw [h]
            exact hx
          exact hx'.1
        exact absurd (sup_le hLY hSY) (not_le_of_gt hYH)
    intro y hy
    obtain ⟨l, hl, s, hs, rfl⟩ := zb_mem_sup hSN (hYH.le hy)
    have hlY : l ∈ Y := by
      have := Y.mul_mem hy (Y.inv_mem (hSY hs))
      simpa [mul_assoc] using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hY1 ⟨hlY, hl⟩)) (Subgroup.mem_sup_right hs)
  have hnn' : ¬ (L ⊔ S) ≤ Subgroup.normalizer (S : Set G) := by
    intro hH
    apply hnn
    intro l hl
    exact zb_mem_normalizer_inf (hH (Subgroup.mem_sup_left hl)) (Subgroup.le_normalizer hl)
  exact ⟨hSH, hnn', Bor ⊔ S, le_sup_right, hXH, hmaxX⟩

end Parabolic

theorem mem_normalizer_sup1521 {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  refine GoldMLA.mem_normalizer_of_conjByElt_eq ?_
  unfold conjByElt
  rw [Subgroup.map_sup]
  have h1 := GoldMLA.conjByElt_eq_of_mem_normalizer hA
  have h2 := GoldMLA.conjByElt_eq_of_mem_normalizer hB
  unfold conjByElt at h1 h2
  rw [h1, h2]

theorem thompsonJ_le_baum1521 (S : Subgroup G) : thompsonJ S ≤ baum S := by
  refine le_inf (thompsonJ_le_self151 S) fun j hj => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hZ : omegaOneCenterOf (thompsonJ S) ≤ centerOf (thompsonJ S) :=
    (Subgroup.closure_le _).mpr fun x hx => hx.1
  have := Subgroup.mem_centralizer_iff.mp (hZ hh).2 j hj
  exact this.symm

section Baumann

variable [Finite G]

theorem borel_le_normalizer_thompsonJ_of_normalizes {L S : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hLn : IsLin2Type L n) (hshort : IsShort2 L) (hS2 : IsPGroup 2 ↥S)
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hsyl : IsSylowTwoOf (S ⊓ L) L)
    (hth : ⁅L, thompsonJ S⁆ = L) :
    L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤
      Subgroup.normalizer (thompsonJ S : Set G) := by
  have hmin : IsMinimalParabolic S (L ⊔ S) := isMinimalParabolic_l2 hn hLn hS2 hSN hsyl
  have hLH : L ≤ L ⊔ S := le_sup_left
  have hHN : L ⊔ S ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hSN
  have hsub : (L.subgroupOf (L ⊔ S)).IsSubnormal :=
    Subgroup.Normal.isSubnormal ((Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hHN)
  have hblk : IsChi0Block (L ⊔ S) L := ⟨⟨hshort, hLH, hsub⟩, Or.inl ⟨n, by omega, hLn⟩⟩
  obtain ⟨hBN, hBsyl⟩ := C56.baumann_single hmin hblk (Or.inl ⟨n, by omega, hLn⟩) hth rfl hSN
  have hc := C56.baumann_c542 hmin hblk (by omega) hLn hth rfl hSN
  set P : Subgroup G := baum S with hP
  have hPS : P ≤ S := inf_le_left
  have hLP : L ≤ L ⊔ P := le_sup_left
  have hPN : L ⊔ P ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hBN
  have hsubP : (L.subgroupOf (L ⊔ P)).IsSubnormal :=
    Subgroup.Normal.isSubnormal ((Subgroup.normal_subgroupOf_iff_le_normalizer hLP).mpr hPN)
  have hPL : IsSylowTwoOf (P ⊓ L) L := RankOneRecog.isSylowTwoOf_inf_of_subnormal hBsyl hLP hsubP
  have hPLS : P ⊓ L = S ⊓ L := by
    refine le_antisymm (inf_le_inf_right L hPS) ?_
    exact ((A4.isSylowTwoOf_iff_maximal.mp hPL).2.2 (S ⊓ L) inf_le_right
      (hS2.to_le inf_le_left) (inf_le_inf_right L hPS))
  have hOP : pCoreOf 2 (L ⊔ P) ≤ P := pCoreOf_le_of_isSylowTwoOf hBsyl
  have hPeq : P = (S ⊓ L) ⊔ pCoreOf 2 (L ⊔ P) := by
    refine le_antisymm (hPLS ▸ hc) (sup_le ?_ hOP)
    exact hPLS ▸ inf_le_left
  intro b hb
  have hbO : b ∈ Subgroup.normalizer (pCoreOf 2 (L ⊔ P) : Set G) :=
    le_normalizer_pCoreOf 2 (L ⊔ P) (hLP hb.1)
  have hbP : b ∈ Subgroup.normalizer (P : Set G) := by
    rw [hPeq]
    exact mem_normalizer_sup1521 hb.2 hbO
  have h2 := normalizer_le_normalizer_thompsonJ P hbP
  rwa [B6.thompsonJ_eq_of_le (thompsonJ_le_baum1521 S) hPS] at h2

end Baumann

theorem le_normalizer_of_commutator_eq1521 {L J : Subgroup G} (h : ⁅L, J⁆ = L) :
    J ≤ Subgroup.normalizer (L : Set G) := by
  have key : ∀ j ∈ J, ∀ l ∈ L, j * l * j⁻¹ ∈ L := by
    intro j hj l hl
    have h1 : ⁅l⁻¹, j⁆ ∈ ⁅L, J⁆ := Subgroup.commutator_mem_commutator (L.inv_mem hl) hj
    rw [h] at h1
    have e : l * ⁅l⁻¹, j⁆ = j * l * j⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [← e]
    exact L.mul_mem hl h1
  intro j hj
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key j hj x hx, fun hx => ?_⟩
  have := key j⁻¹ (J.inv_mem hj) _ hx
  simpa [mul_assoc] using this

section BaumannL2

variable [Finite G]

theorem borel_le_normalizer_thompsonJ_l2 {L S : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hLn : IsLin2Type L n) (hshort : IsShort2 L) (hS2 : IsPGroup 2 ↥S)
    (hsyl : IsSylowTwoOf (S ⊓ L) L) (hth : ⁅L, thompsonJ S⁆ = L) :
    L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤
      Subgroup.normalizer (thompsonJ S : Set G) := by
  set R : Subgroup G := S ⊓ Subgroup.normalizer (L : Set G) with hR
  have hJN : thompsonJ S ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_commutator_eq1521 hth
  have hJR : thompsonJ S ≤ R := le_inf (thompsonJ_le_self151 S) hJN
  have hRS : R ≤ S := inf_le_left
  have hJeq : thompsonJ R = thompsonJ S := B6.thompsonJ_eq_of_le hJR hRS
  have hRL : R ⊓ L = S ⊓ L := le_antisymm (fun x hx => ⟨hx.1.1, hx.2⟩)
    (fun x hx => ⟨⟨hx.1, Subgroup.le_normalizer hx.2⟩, hx.2⟩)
  have h := borel_le_normalizer_thompsonJ_of_normalizes hn hLn hshort (hS2.to_le hRS)
    inf_le_right (hRL ▸ hsyl) (by rw [hJeq]; exact hth)
  rw [hRL, hJeq] at h
  exact h

end BaumannL2

end CFSG.Quasithin
