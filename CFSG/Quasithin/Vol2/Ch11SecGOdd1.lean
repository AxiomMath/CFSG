module

public import CFSG.Quasithin.Vol2.Ch11SecD551B
public import CFSG.Quasithin.Vol2.Ch11SecGBasic
public import CFSG.Quasithin.Vol2.Ch11SecGFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G]

theorem le_normalizer_conjClosure_of {U S K : Subgroup G}
    (hKU : K ≤ Subgroup.normalizer (U : Set G)) (hSK : S ≤ Subgroup.normalizer (K : Set G)) :
    K ≤ Subgroup.normalizer (conjClosure U S : Set G) := by
  have key : ∀ k ∈ K, ∀ x ∈ conjClosure U S, k * x * k⁻¹ ∈ conjClosure U S := by
    intro k hk x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨s, hs, u, hu, rfl⟩ := hx
      have hk' : s⁻¹ * k * s ∈ K := by
        have h1 := (Subgroup.mem_normalizer_iff.mp (hSK (inv_mem hs)) k).mp hk
        simpa using h1
      have hu' : (s⁻¹ * k * s) * u * (s⁻¹ * k * s)⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hKU hk') u).mp hu
      have h2 := mem_conjClosure hs hu'
      convert h2 using 1
      group
    | one => simp
    | mul x y _ _ ihx ihy =>
      have h2 := (conjClosure U S).mul_mem ihx ihy
      convert h2 using 1
      group
    | inv x _ ih =>
      have h2 := (conjClosure U S).inv_mem ih
      convert h2 using 1
      group
  intro k hk
  exact SecD.mem_normalizer_of_conj (key k hk) fun x hx => by
    simpa using key k⁻¹ (inv_mem hk) x hx

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem card_conjSub_V₁ (h1102 : Stmt11_0_2) (h1141 : Stmt11_4_1) (h : Hyp11 G T L I n)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (m : G) :
    Nat.card (conjSub m V₁) = 2 ^ n := by
  have hset := SecD.natSetting11_of h1102 h1141 h hV₁
  rw [card_conjSub]
  have h1 := SecA.IsVi.relIndex_eq hV₁
  rw [hset.cV, Subgroup.relIndex_bot_left, mul_one] at h1
  exact h1

theorem conjSub_kOf_eq_of_mem (hTI : SecD.PointsTIFact) (hPt : PointConjFact)
    (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1141 : Stmt11_4_1) (h1142 : Stmt11_4_2)
    (h1151 : Stmt11_5_1) (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    {g z : G} (hz : z ∈ V₁) (hzg : z ∈ conjSub g V₁) (hz1 : z ≠ 1) :
    conjSub g (KOf L V₁ V₁) = KOf L V₁ V₁ := by
  set V := fsuV T I with hVdef
  have hset := SecD.natSetting11_of h1102 h1141 h hV₁
  have hkind := h1151 G T L I n h
  have hV₁V := SecA.IsVi.le_fsuV hV₁
  obtain ⟨y, hy, hgy⟩ := exists_centralizer_conjSub_eq h1141 h hV₁ (hV₁V hz) hz1
    (conjSub_mono g hV₁V hzg)
  have hmV : y⁻¹ * g ∈ Subgroup.normalizer (V : Set G) := by
    apply mem_normalizer_of_conjSub_eq
    rw [conjSub_mul, hgy, conjSub_conjSub_inv]
  have hmL := SecA.normalizer_fsuV_le h331 h hmV
  have hE := isEndStable_conjSub hmL hmV (SecA.IsVi.isEndStable hV₁)
  have hPV : conjSub (y⁻¹ * g) V₁ ≤ V := by
    have h1 := conjSub_mono (y⁻¹ * g) hV₁V
    rwa [F7.conjSub_eq_of_mem_normalizer hmV] at h1
  obtain ⟨l, hl, hPl⟩ := hPt G T L I n V₁ _ hset hkind hV₁ hPV hE
    (card_conjSub_V₁ h1102 h1141 h hV₁ _)
  have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hy
  have hzm : z ∈ conjSub (y⁻¹ * g) V₁ := by
    rw [mem_conjSub]
    have e : (y⁻¹ * g)⁻¹ * z * (y⁻¹ * g) = g⁻¹ * z * g := by
      calc (y⁻¹ * g)⁻¹ * z * (y⁻¹ * g) = g⁻¹ * (y * z) * y⁻¹ * g := by group
        _ = g⁻¹ * (z * y) * y⁻¹ * g := by rw [hyz]
        _ = g⁻¹ * z * g := by group
    rw [e]
    exact mem_conjSub.mp hzg
  have hne : V₁ ⊓ conjSubgroup V₁ l ≠ ⊥ := fun hbot => hz1 (by
    have hz' : z ∈ V₁ ⊓ conjSubgroup V₁ l := ⟨hz, hPl ▸ hzm⟩
    rw [hbot] at hz'
    exact Subgroup.mem_bot.mp hz')
  have hl1 := hTI G T L I n V₁ hset hV₁ l hl hne
  have hmV₁ : y⁻¹ * g ∈ Subgroup.normalizer (V₁ : Set G) :=
    mem_normalizer_of_conjSub_eq (by rw [hPl, hl1])
  have hyK : y ∈ Subgroup.normalizer (KOf L V₁ V₁ : Set G) :=
    centralizer_le_normalizer_kOf hTI h1102 h1141 h1142 h hV₁ hz hz1 hy
  calc conjSub g (KOf L V₁ V₁) = conjSub y (conjSub (y⁻¹ * g) (KOf L V₁ V₁)) := by
        rw [← conjSub_mul, mul_inv_cancel_left]
    _ = conjSub y (KOf L V₁ V₁) := by
        rw [F7.conjSub_eq_of_mem_normalizer (SecD.normalizer_le_normalizer_kOf L V₁ V₁ hmV₁)]
    _ = KOf L V₁ V₁ := F7.conjSub_eq_of_mem_normalizer hyK

theorem inf_conjSub_eq_bot (hTI : SecD.PointsTIFact) (hPt : PointConjFact)
    (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1141 : Stmt11_4_1) (h1142 : Stmt11_4_2)
    (h1151 : Stmt11_5_1) (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    {g : G} (hgO : ¬ fsuV T I ≤ conjSub g (pCoreOf 2 (KOf L V₁ V₁ ⊔ T)))
    (hU : ∃ k ∈ KOf L V₁ V₁ ⊔ T, conjClosure (fsuV T I) (KOf L V₁ V₁ ⊔ T) ≤
      conjSub (g * k) (ROf T L V₁)) :
    V₁ ⊓ conjSub g V₁ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := KOf L V₁ V₁ with hKdef
  set H₁ := K ⊔ T with hH₁def
  set U := conjClosure (fsuV T I) H₁ with hUdef
  by_contra hne
  obtain ⟨⟨z, hzmem⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hz1' : z ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  have hKg := conjSub_kOf_eq_of_mem hTI hPt h331 h1102 h1141 h1142 h1151 h hV₁ hzmem.1 hzmem.2
    hz1'
  obtain ⟨k, hk, hUk⟩ := hU
  apply hgO
  have hTK : T ≤ Subgroup.normalizer (K : Set G) :=
    (SecA.IsVi.le_normalizer hV₁).trans (SecD.normalizer_le_normalizer_kOf L V₁ V₁)
  have hH₁K : H₁ ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  set S := conjSub (g * k) T with hSdef
  have hS2 : IsPGroup 2 S := F7.isPGroup_conjSub h.fsu.sylow.1
  have hUS : U ≤ S := hUk.trans (conjSub_mono _ (SecD.ROf_le_T h V₁))
  have hSeq : S = conjSub g (conjSub k T) := conjSub_mul g k T
  have hH : conjSub g H₁ = K ⊔ S := by
    have e1 : H₁ = K ⊔ conjSub k T := by
      conv_lhs => rw [← F7.conjSub_eq_of_mem hk]
      rw [hH₁def, conjSub_sup, F7.conjSub_eq_of_mem_normalizer (hH₁K hk)]
    rw [hSeq, e1, conjSub_sup, hKg]
  have hSH : S ≤ conjSub g H₁ := hH ▸ le_sup_right
  have hSK : S ≤ Subgroup.normalizer (K : Set G) := by
    have h1 := conjSub_le_normalizer (g := g) hH₁K
    rw [hKg] at h1
    exact hSH.trans h1
  have hKU : K ≤ Subgroup.normalizer (U : Set G) :=
    le_sup_left.trans (le_normalizer_conjClosure _ _)
  set N := conjClosure U S with hNdef
  have hNS : N ≤ S := conjClosure_le fun s hs u hu =>
    S.mul_mem (S.mul_mem hs (hUS hu)) (S.inv_mem hs)
  have hNnorm : conjSub g H₁ ≤ Subgroup.normalizer (N : Set G) := by
    rw [hH]
    exact sup_le (le_normalizer_conjClosure_of hKU hSK) (le_normalizer_conjClosure U S)
  have hNO : N ≤ pCoreOf 2 (conjSub g H₁) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hNS.trans hSH) hNnorm (hS2.to_le hNS)
  rw [← pCoreOf_conjSub]
  exact (le_conjClosure _ _).trans ((le_conjClosure U S).trans hNO)

end CFSG.Quasithin.Vol2.Ch11.SecG
