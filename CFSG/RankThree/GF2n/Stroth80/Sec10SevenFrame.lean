module

public import CFSG.RankThree.GF2n.Stroth80.Sec10SevenRoots
public import CFSG.RankThree.GF2n.Stroth80.Sec10SevenChi
public import CFSG.RankThree.GF2n.Stroth80.Sec10Six
public import CFSG.RankThree.GF2n.Stroth80.Sec10Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Good103.exists_root_le_inf {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G}
    (ht : Good103 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {X : Subgroup G} {y : G}
    (hsy : Sit M Q Z X y) {γ : G} (hγ : γ ∈ Q ⊓ QB Y ⊓ QB X) (hγ1 : γ ≠ 1) :
    ∃ D : Subgroup G, Ctx M Q Z D ∧ γ ∈ D ∧ D ≤ Q ⊓ QB Y ⊓ QB X := by
  have hZY : Z ⊓ QB Y = ⊥ := Z_inf_QB_eq_bot hs (smith_1_12 hs)
  have hγV : γ ∈ Vt M (LB M Q B) B Z t := by
    rw [Good103.Vt_eq ht hs]
    exact Subgroup.mem_sup_left hγ.1
  have hγZ : γ ∉ Z := by
    intro hz
    have hmem : γ ∈ Z ⊓ QB Y := ⟨hz, hγ.1.2⟩
    rw [hZY, Subgroup.mem_bot] at hmem
    exact hγ1 hmem
  obtain ⟨D, hD, hγD, hDY, -⟩ :=
    Sit.exists_root_group hs hγ.1 hγ1 (ht.1.isRoot_of_mem_Vt H hγV hγZ)
  have hne : D ≠ X := by
    intro h
    apply hsy.notQ
    exact hD.le (h ▸ hsy.mem)
  have hDX : D ≤ QB X :=
    hc.hyp.le_QB_of_mem_of_mem_QB hD.conj hsy.conj hne hγD hγ1 hγ.2
  exact ⟨D, hD, hγD, le_inf (le_inf hD.le hDY) hDX⟩

theorem Good103.exists_two_roots {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G}
    (ht : Good103 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {X : Subgroup G} {y : G}
    (hsy : Sit M Q Z X y) (hC : Nat.card Z < Nat.card ↥(Q ⊓ QB Y ⊓ QB X)) :
    ∃ D₁ D₂ : Subgroup G, Ctx M Q Z D₁ ∧ Ctx M Q Z D₂ ∧ D₁ ≤ Q ⊓ QB Y ⊓ QB X ∧
      D₂ ≤ Q ⊓ QB Y ⊓ QB X ∧ D₁ ≠ D₂ ∧ (D₁ ⊔ Z) ⊓ (D₂ ⊔ Z) = Z := by
  have hCbot : (Q ⊓ QB Y ⊓ QB X : Subgroup G) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hC
    have := Nat.card_pos (α := Z)
    omega
  obtain ⟨γ₁, hγ₁C, hγ₁1⟩ :=
    (Subgroup.bot_or_exists_ne_one (Q ⊓ QB Y ⊓ QB X)).resolve_left hCbot
  obtain ⟨D₁, hD₁, hγ₁D₁, hD₁C⟩ := Good103.exists_root_le_inf H ht hs hsy hγ₁C hγ₁1
  obtain ⟨g₁, hg₁⟩ := hD₁.conj
  have hD₁card : Nat.card ↥D₁ = Nat.card Z := by
    rw [hg₁]
    exact card_conjSubgroup g₁ Z
  have hnotle : ¬ (Q ⊓ QB Y ⊓ QB X : Subgroup G) ≤ D₁ := by
    intro hle
    have hcard : Nat.card ↥(Q ⊓ QB Y ⊓ QB X) ≤ Nat.card ↥D₁ :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective _)
    omega
  obtain ⟨γ₂, hγ₂C, hγ₂D₁⟩ := IsConcreteLE.not_le_iff_exists.1 hnotle
  have hγ₂1 : γ₂ ≠ 1 := by
    intro h1
    exact hγ₂D₁ (h1 ▸ D₁.one_mem)
  obtain ⟨D₂, hD₂, hγ₂D₂, hD₂C⟩ := Good103.exists_root_le_inf H ht hs hsy hγ₂C hγ₂1
  have hne : D₁ ≠ D₂ := fun heq => hγ₂D₁ (heq ▸ hγ₂D₂)
  have hCZ : (Q ⊓ QB Y ⊓ QB X : Subgroup G) ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzC, hzZ⟩
    have hzY : z ∈ Z ⊓ QB Y := ⟨hzZ, hzC.1.2⟩
    rwa [Z_inf_QB_eq_bot hs (smith_1_12 hs), Subgroup.mem_bot] at hzY
  exact ⟨D₁, D₂, hD₁, hD₂, hD₁C, hD₂C, hne,
    hc.hyp.sup_inf_sup_eq hD₁.conj hD₂.conj hne hD₁C hD₂C
      (inf_le_left.trans inf_le_left) hCZ⟩

private theorem Sit.exists_root_conj {X : Subgroup G} {y : G} (hsy : Sit M Q Z X y) :
    ∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = y := by
  obtain ⟨g, hg⟩ := hsy.conj
  have hyZ : g⁻¹ * y * g ∈ Z := by
    have h : y ∈ conjSubgroup g Z := hg ▸ hsy.mem
    exact mem_conjSubgroup.mp h
  refine ⟨g, g⁻¹ * y * g, hyZ, ?_, by group⟩
  intro h1
  apply hsy.ne_one
  calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

private theorem card_centralizer_mul_pow_le_of_Ut {y : G} {m k : ℕ}
    (hC : Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set G)) * Nat.card ↥(Ut Q Z y) =
      Nat.card Q * Nat.card Z)
    (hU : Nat.card ↥(Ut Q Z y) = Nat.card Z ^ (2 * k + 1)) (hmk : m ≤ k) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set G)) * Nat.card Z ^ (2 * m) ≤
      Nat.card Q := by
  have hq : 0 < Nat.card Z := Nat.card_pos
  have hU' : Nat.card ↥(Ut Q Z y) = Nat.card Z ^ (2 * k) * Nat.card Z := by
    rw [hU, pow_succ]
  have hCeq : Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set G)) *
      Nat.card Z ^ (2 * k) = Nat.card Q := by
    refine Nat.eq_of_mul_eq_mul_right hq ?_
    calc Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set G)) * Nat.card Z ^ (2 * k) *
        Nat.card Z
        = Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set G)) *
          (Nat.card Z ^ (2 * k) * Nat.card Z) := by ring
      _ = Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set G)) *
          Nat.card ↥(Ut Q Z y) := by rw [hU']
      _ = Nat.card Q * Nat.card Z := hC
  calc Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set G)) * Nat.card Z ^ (2 * m)
      ≤ Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set G)) * Nat.card Z ^ (2 * k) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq (by omega))
    _ = Nat.card Q := hCeq

theorem Sit.root_frame_facts (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) (h103b : Stroth103bStatement)
    {hc : Ctx M Q Z B} {n m : ℕ} (H : Sec10Hyp hc n)
    (hge3 : ∀ s : G, Good101 M Q Z B s → ¬ SLMNat hc s 2)
    (hmin : ∀ (s : G) (k : ℕ), Good101 M Q Z B s → SLMNat hc s k → m ≤ k)
    {X : Subgroup G} {y : G} (hsy : Sit M Q Z X y) {D₁ D₂ : Subgroup G}
    (hD₁ : Ctx M Q Z D₁) (hD₂ : Ctx M Q Z D₂) (hyD₁ : y ∈ QB D₁) (hyD₂ : y ∈ QB D₂)
    (hsup : (D₁ ⊔ Z) ⊓ (D₂ ⊔ Z) = Z) :
    (∀ w ∈ Q, ∀ z ∈ Z, w * y * w⁻¹ = y * z → z = 1) ∧
    Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set G)) * Nat.card Z ^ (2 * m) ≤ Nat.card Q ∧
    Wt Q (Q ⊓ Subgroup.centralizer ({y} : Set G)) = Ut Q Z y ∧
    ∀ u ∈ Ut Q Z y, ∃ x ∈ Q, ∃ z ∈ Z, u = ⁅x, y⁆ * z := by
  obtain ⟨r₁, hr₁, rfl⟩ := H.rootTrans h34 hspread D₁ hD₁
  obtain ⟨r₂, hr₂, rfl⟩ := H.rootTrans h34 hspread D₂ hD₂
  have hD₂eq : conjSubgroup (r₂ * r₁⁻¹) (conjSubgroup r₁ B) = conjSubgroup r₂ B := by
    rw [conjSubgroup_conjSubgroup]
    congr 1
    group
  have hBr : (conjSubgroup r₁ B ⊔ Z) ⊓
      (conjSubgroup (r₂ * r₁⁻¹) (conjSubgroup r₁ B) ⊔ Z) = Z := by
    rw [hD₂eq]
    exact hsup
  have hyD₂' : y ∈ QB (conjSubgroup (r₂ * r₁⁻¹) (conjSubgroup r₁ B)) := by
    rw [hD₂eq]
    exact hyD₂
  have H₁ : Sec10Hyp (hc.conj_of_mem hr₁) n := H.conj_of_mem hr₁
  have hge3₁ : ∀ s : G, Good101 M Q Z (conjSubgroup r₁ B) s →
      ¬ SLMNat (hc.conj_of_mem hr₁) s 2 := noSL2_conj_of_mem hge3 hr₁
  have hR : Rt M (LB M Q (conjSubgroup r₁ B)) y ≠ LB M Q (conjSubgroup r₁ B) :=
    H₁.Rt_ne_LB_of_mem_QB h34 (M.mul_mem hr₂ (M.inv_mem hr₁)) hBr hsy.memM hyD₂'
  have hroot := Sit.exists_root_conj hsy
  have hy101 : Good101 M Q Z (conjSubgroup r₁ B) y :=
    ⟨hroot, hsy.memM, hsy.notQ, hyD₁, hR⟩
  have hy103 : Good103 M Q Z (conjSubgroup r₁ B) y :=
    ⟨hy101, h103b G M Q Z (conjSubgroup r₁ B) (hc.conj_of_mem hr₁) n H₁ hge3₁ y hy101⟩
  obtain ⟨k, -, hk⟩ := SLlike.exists_SLMNat (H₁.slLike hy101)
  have hmk : m ≤ k := Good101.le_of_min_conj hmin hr₁ hy101 hk
  have hnf := Good103.no_fuse_of_noSL2 h34 h311a hspread H₁ hge3₁ hy103
  have hU := Good103.card_Ut_eq h34 h311a hspread H₁ hy103 hk
  have hCcard := Ctx.card_centralizer_mul_card_Ut (hc := hc.conj_of_mem hr₁)
    (t := y) hy101.mem_LB hnf
  have hWt := Ctx.Wt_centralizer_eq_Ut (hc := hc.conj_of_mem hr₁) (t := y) hy101.mem_LB hnf
  refine ⟨hnf, card_centralizer_mul_pow_le_of_Ut hCcard hU hmk, hWt,
    fun u hu => Ctx.exists_comm_mul_of_mem_Ut (hc := hc.conj_of_mem hr₁)
      (t := y) (u := u) hy101.mem_LB hu⟩

end CFSG.RankThree.GF2n.Stroth80
