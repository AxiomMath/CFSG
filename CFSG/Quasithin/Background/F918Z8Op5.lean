module

public import CFSG.Quasithin.Background.F918Z8Op3
public import CFSG.Quasithin.Background.F918Z8Op4a
public import CFSG.Quasithin.Background.F918Z8Op4b
public import CFSG.Quasithin.Background.F918Z8Op4c
public import CFSG.Quasithin.Background.F918Z8Op4d
public import CFSG.Quasithin.Background.F918Z8Def3
public import CFSG.Quasithin.Background.F918Z8a
public import CFSG.Quasithin.Background.F918Z8b

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem d321OpPrimeC_of_core (hL38 : D3L38) (hcore : D321OpCore) :
    D321OpPrimeC := by
  intro W _ _ M Mp T L V t hstd htT htL hMp htriv g hgM hgc p hp hp2 hpL hk u hu
  have hgL' := hcore W M Mp T L V t hstd htT htL hMp g hgM hgc p hp hp2 hpL hk
  have hU : commV L ≤ fixV (conjAutSub t L) := (d321_struct hL38 hstd htT htL hMp htriv).2
  exact hU hu g hgL'


theorem excPair_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {p : ℕ} (h : ExcPair X p) :
    ExcPair Y p := by
  obtain ⟨q, hq, h3, h4, hpq, hpsl⟩ := h
  exact ⟨q, hq, h3, h4, hpq, isPSL_congr e hpsl⟩

theorem a38_invSylAll {G : Type} [Group G] {L : Subgroup G} (hL : A38Types ↥L) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpL : p ∣ Nat.card L) (hexc : ¬ ExcPair ↥L p) :
    InvSylAll L p := by
  rcases hL with ⟨n, hn⟩ | ⟨n, hn⟩ | hJ | ⟨q, hq, hq3, hpsl⟩
  · exact a38_invSyl_psl2even hn hp hp2 hpL
  · exact a38_invSyl_sz hn hp hp2 hpL
  · exact a38_invSyl_j1 hJ hp hp2 hpL
  · exact a38_invSyl_psl2odd hq hq3 hpsl hp hp2 hpL fun h => hexc ⟨q, hq, hq3, h.2, h.1, hpsl⟩

theorem d321OpCore_of_inputs (hL38 : D3L38) (hExc : D321OpExc) :
    D321OpCore := by
  intro W _ _ M Mp T L V t hstd htT htL hMp g hgM hgc p hp hp2 hpL hk
  by_cases hex : ExcPair ↥L p
  · exact hExc W M Mp T L V t hstd htT htL hMp g hgM hgc p hp hp2 hpL hk hex
  obtain ⟨hA38, hcomm, hinf, -⟩ := hL38 W M Mp T L V hstd t htT htL hMp
  have hD := hstd.hyp
  have hLs : IsSimpleGroup ↥L := Vol2Native.L122A.isSimpleGroup_of_a38Types hA38
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hD.quasi.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  have hLM : L ≤ M := le_of_mem_cComp hD.comp
  have htM : t ∈ M := hD.sylow.1 htT
  have hL'M : conjAutSub t L ≤ M := by
    intro x hx
    have h1 : t⁻¹ * x * t ∈ L := mem_conjAutSub_iff.mp hx
    have e : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem htM (hLM h1)) (M.inv_mem htM)
  have hcommAll : ∀ a ∈ L, ∀ b ∈ conjAutSub t L, a * b = b * a := by
    intro a ha b hb
    have hle : L ≤ Subgroup.centralizer ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact ((Subgroup.mem_centralizer_iff.mp (hle ha)) b hb).symm
  have hLc : ∀ a ∈ L, (∀ b ∈ L, a * b = b * a) → a = 1 := by
    intro a ha hac
    have hmem : (⟨a, ha⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro b
      exact Subtype.ext (hac b b.2).symm
    rcases hLs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h | h
    · rw [h, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      apply hxy
      have hx : x ∈ Subgroup.center ↥L := by rw [h]; exact Subgroup.mem_top x
      exact ((Subgroup.mem_center_iff.mp hx) y).symm
  have hgn : ∀ x ∈ conjAutSub t L, g * x * g⁻¹ ∈ conjAutSub t L := by
    intro x hx
    have hgtM : g * t ∈ M := M.mul_mem hgM htM
    have hmem : g * x * g⁻¹ ∈ conjAutSub (g * t) L := by
      rw [mem_conjAutSub_iff]
      have h1 : t⁻¹ * x * t ∈ L := mem_conjAutSub_iff.mp hx
      have e : (g * t)⁻¹ * (g * x * g⁻¹) * (g * t) = t⁻¹ * x * t := by group
      rw [e]
      exact h1
    rcases d321a_perm hLs hnab hcomm hMp hD.Mp_normal hgtM with h | h
    ·
      rw [h] at hmem
      have hxL : x ∈ L := by
        have hc := hgc _ hmem
        have h1 : g⁻¹ * (g * x * g⁻¹) * g = g * x * g⁻¹ := by
          calc g⁻¹ * (g * x * g⁻¹) * g = g⁻¹ * ((g * x * g⁻¹) * g) := by group
            _ = g⁻¹ * (g * (g * x * g⁻¹)) := by rw [hc]
            _ = g * x * g⁻¹ := by group
        have h2 : x = g * x * g⁻¹ := by
          calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
            _ = g * x * g⁻¹ := h1
        rw [h2]
        exact hmem
      have hx1 : x ∈ L ⊓ conjAutSub t L := ⟨hxL, hx⟩
      rw [hinf, Subgroup.mem_bot] at hx1
      rw [hx1]
      simp
    · rw [h] at hmem
      exact hmem
  have hpL' : p ∣ Nat.card (conjAutSub t L) := by
    rw [← Nat.card_congr (d321b_conjEquiv t L).toEquiv]
    exact hpL
  have hex' : ¬ ExcPair ↥(conjAutSub t L) p := fun h =>
    hex (excPair_congr (d321b_conjEquiv t L).symm h)
  have : Fact p.Prime := ⟨hp⟩
  exact opq_core hD.qsqtk hp2 hLM hL'M hcommAll hLc hpL hpL'
    (a38_invSylAll hA38 hp hp2 hpL hex)
    (a38_invSylAll (a38Types_congr (d321b_conjEquiv t L) hA38) hp hp2 hpL' hex')
    hgM hgc hgn hk

theorem d321OpPrimeC_of_inputs (hL38 : D3L38) (hExc : D321OpExc) :
    D321OpPrimeC :=
  d321OpPrimeC_of_core hL38 (d321OpCore_of_inputs hL38 hExc)

end CFSG.Quasithin
