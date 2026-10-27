module

public import CFSG.Quasithin.Vol2.Ch11SecFQ1
public import CFSG.Quasithin.Vol2.Ch11SecFFacts3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.QuasithinUnique.C5 (conjSubgroup_normalizer conjSubgroup_centralizer conjSubgroup_eq_self)

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ V₃ : Subgroup G}

theorem commutator_kY_le_of (h1154 : Stmt11_5_4) (h1156 : Stmt11_5_6) (h : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) {X P : Subgroup G} (hX : IsCartanX T L X) (hPX : P = ⁅P, X⁆)
    (hPT : P ≤ T)
    (hΦ : (frattini ↥P).map P.subtype ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)))
    (hPO : P ≤ pCoreOf 2 (L ⊔ T)) :
    ⁅P, KOf L V₁ V₁ ⊔ (Subgroup.centralizer (V₁ : Set G) ⊓
        sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)))⁆ ≤
      pCoreOf 2 (KOf L V₁ V₁ ⊔ (Subgroup.centralizer (V₁ : Set G) ⊓
        sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := KOf L V₁ V₁ with hKdef
  set Y := Subgroup.centralizer (V₁ : Set G) ⊓ sectionCentralizer K (pCoreOf 2 K) with hYdef
  obtain ⟨-, -, -, -, h64, h65, -⟩ := h1156 G T L I n V₁ X (Subgroup.normalizer (V₁ : Set G))
    h hV₁ hX (inH_normalizer_V₁ h hV₁) (normalizer_V₁_not_le h1154 h hV₁) le_rfl
  have hPY : ⁅P, Y⁆ ≤ pCoreOf 2 Y := h64 P hPX hPT hΦ
  have hPKT : P ≤ pCoreOf 2 (K ⊔ T) := by
    calc P = ⁅P, X⁆ := hPX
      _ ≤ ⁅pCoreOf 2 (L ⊔ T), X⁆ := Subgroup.commutator_mono hPO le_rfl
      _ ≤ pCoreOf 2 (K ⊔ T) := h65
  have hG₁K : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    SecD.normalizer_le_normalizer_kOf L V₁ V₁
  have hG₁Y : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (Y : Set G) :=
    SecD.normalizer_le_normalizer_Y L V₁
  have hPK : ⁅P, K⁆ ≤ pCoreOf 2 K :=
    commutator_le_pCoreOf_of_le ((SecA.IsVi.le_normalizer hV₁).trans hG₁K) hPKT
  have hKY : K ⊔ Y ≤ Subgroup.normalizer (V₁ : Set G) :=
    sup_le (kOf_le_normalizer_V₁ L V₁) (Y_le_normalizer_V₁ L V₁)
  have hKYO : K ⊔ Y ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ Y) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hOK : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ Y) :=
    pCoreOf_le_pCoreOf_of_le_normalizer le_sup_left (hKY.trans hG₁K)
  have hOY : pCoreOf 2 Y ≤ pCoreOf 2 (K ⊔ Y) :=
    pCoreOf_le_pCoreOf_of_le_normalizer le_sup_right (hKY.trans hG₁Y)
  exact commutator_sup_right_le (le_sup_left.trans hKYO) (le_sup_right.trans hKYO)
    (hPK.trans hOK) (hPY.trans hOY)

theorem commutator_pCoreOf_kY_le (L V₁ : Subgroup G) :
    ⁅pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)), KOf L V₁ V₁ ⊔
        (Subgroup.centralizer (V₁ : Set G) ⊓
          sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)))⁆ ≤
      pCoreOf 2 (KOf L V₁ V₁ ⊔ (Subgroup.centralizer (V₁ : Set G) ⊓
        sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKY : KOf L V₁ V₁ ⊔ (Subgroup.centralizer (V₁ : Set G) ⊓
      sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁))) ≤
      Subgroup.normalizer (V₁ : Set G) :=
    sup_le (kOf_le_normalizer_V₁ L V₁) (Y_le_normalizer_V₁ L V₁)
  have hG₁KY := SecD.le_normalizer_sup (SecD.normalizer_le_normalizer_kOf L V₁ V₁)
    (SecD.normalizer_le_normalizer_Y L V₁)
  have hQ := CFSG.LieType.BorelTits.pCoreOf_le 2 (Subgroup.normalizer (V₁ : Set G))
  have h1 := commutator_le_inf_of_le_normalizer (hQ.trans hG₁KY)
    (hKY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
  refine h1.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left))
  exact fun k hk => SecD.mem_normalizer_inf
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hKY hk)) (Subgroup.le_normalizer hk)

theorem exists_decomp_opp (hTr : FactSp4Trans) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1110 : Stmt11_1_0) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n)
    {y : G} (hy : y ∈ L) (hopp : conjSubgroup V₁ y ⊓ V₃ = ⊥) :
    ∀ g ∈ Subgroup.normalizer (V₁ : Set G),
      ∃ x ∈ KOf L V₁ V₁ ⊔ (Subgroup.centralizer (V₁ : Set G) ⊓
          sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁))),
        ∃ s ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G) ⊓
          Subgroup.normalizer ((conjSubgroup V₁ y : Subgroup G) : Set G), g = x * s := by
  intro g hg
  obtain ⟨x, hx, m, hm, rfl⟩ := exists_decomp h1143 h hV₁ g hg
  have hmV := inf_normalizer_V₁_le_normalizer_fsuV h1103 h hV₁ hm
  have hn : 1 ≤ n := by have := h.one_lt; omega
  have hnot : ¬ KindSL3 L (fsuV T I) n := fun h3 => SecA.kind_not_SL3_Sp4 hn h3 hk
  have hm3 : m ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₃ : Set G) := by
    rw [((h1110 G T L I n h).2.2 V₁ V₃ hV₁ hV₃).2 hnot]
    exact hm
  obtain ⟨l, hl, heq⟩ := hTr G T L I n V₁ V₃ (SecD.natSetting11_of h1102 h1141 h hV₁) hk hV₁ hV₃
    y hy hopp m⁻¹ (Subgroup.inv_mem _ hm.1) (Subgroup.inv_mem _ hmV) (Subgroup.inv_mem _ hm.2)
    (Subgroup.inv_mem _ hm3.2)
  have hlm : l * m ∈ Subgroup.normalizer ((conjSubgroup V₁ y : Subgroup G) : Set G) := by
    rw [← conjSubgroup_eq_iff_mem_normalizer, conjSubgroup_conjSubgroup]
    have h2 := congrArg (fun A => conjSubgroup A m) heq
    simp only [conjSubgroup_conjSubgroup, inv_mul_cancel_right] at h2
    rw [mul_assoc] at h2
    exact h2.symm
  have hlL : l ∈ L := ((perfectCore_le _).trans inf_le_left) hl
  have hl₁ : l ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G) :=
    ⟨Subgroup.le_normalizer hlL, SecD.lOf_le_normalizer L V₁ hl⟩
  refine ⟨x * l⁻¹, Subgroup.mul_mem _ hx (Subgroup.mem_sup_left
    (le_conjClosure _ _ (Subgroup.inv_mem _ hl))), l * m,
    ⟨Subgroup.mul_mem _ hl₁ hm, hlm⟩, by group⟩

omit [Finite G] in
theorem mem_normalizer_centralizer' {A : Subgroup G} {s : G}
    (hs : s ∈ Subgroup.normalizer (A : Set G)) :
    s ∈ Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) := by
  rw [← conjSubgroup_eq_iff_mem_normalizer, conjSubgroup_centralizer, conjSubgroup_eq_self hs]

theorem inf_le_normalizer_qOf (h1103 : Stmt11_0_3) (h : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) (y : G) :
    Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G) ⊓
        Subgroup.normalizer ((conjSubgroup V₁ y : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((qOf T I V₁ y : Subgroup G) : Set G) := by
  have hC : Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G) ⊓
      Subgroup.normalizer ((conjSubgroup V₁ y : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (fsuV T I : Set G) : Set G) := fun s hs =>
    mem_normalizer_centralizer' (inf_normalizer_V₁_le_normalizer_fsuV h1103 h hV₁ hs.1)
  have hW : Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G) ⊓
      Subgroup.normalizer ((conjSubgroup V₁ y : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((wH T I V₁ : Subgroup G) : Set G) := fun s hs =>
    le_normalizer_conjClosure _ _ hs.1.2
  have hWy : Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G) ⊓
      Subgroup.normalizer ((conjSubgroup V₁ y : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((conjSubgroup (wH T I V₁) y : Subgroup G) : Set G) := by
    intro s hs
    have h2 : s ∈ conjSubgroup (Subgroup.normalizer (V₁ : Set G)) y := by
      rw [conjSubgroup_normalizer]
      exact hs.2
    rw [mem_conjSubgroup_iff] at h2
    rw [← conjSubgroup_normalizer, mem_conjSubgroup_iff]
    exact le_normalizer_conjClosure _ _ h2
  exact SecD.le_normalizer_sup (fun s hs => SecD.mem_normalizer_inf (hW hs) (hC hs))
    (fun s hs => SecD.mem_normalizer_inf (hWy hs) (hC hs))

theorem cartan_le_inf (hN : SecA.NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) {X : Subgroup G} (hX : IsCartanX T L X) {y : G}
    (hyX : y ∈ Subgroup.normalizer (X : Set G)) :
    X ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G) ⊓
      Subgroup.normalizer ((conjSubgroup V₁ y : Subgroup G) : Set G) := by
  have hXV₁ := SecD.cartan_le_normalizer_V₁ hN h1102 h hV₁ hX
  intro x hx
  have h2 : x ∈ conjSubgroup (Subgroup.normalizer (V₁ : Set G)) y :=
    mem_conjSubgroup_iff.mpr (hXV₁ ((Subgroup.mem_normalizer_iff.mp hyX x).mp hx))
  rw [conjSubgroup_normalizer] at h2
  exact ⟨⟨Subgroup.le_normalizer (hX.1 hx).1, hXV₁ hx⟩, h2⟩

end CFSG.Quasithin.Vol2.Ch11.SecF
