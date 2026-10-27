module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RStmt
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Final
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9N5

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

@[expose] def WPointConcl (M Q Z B : Subgroup G) (t : G) : Prop :=
  (∃ g : G, ∃ b ∈ B, g * t * g⁻¹ = b) → B ≤ QB (Subgroup.zpowers t) →
    ∃ C : Subgroup G, IsConjB M B C ∧ C ≠ B ∧ C ≤ Q ⊓ QB (Subgroup.zpowers t) ⊓ QB B

end HS9

@[expose] def Sec96WStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y → HS9.Sec4Concl M Q Z B X Y →
      HS9.OneConcl hc X Y → HS9.WPointConcl M Q Z B t

@[expose] def Sec57WStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → SLNat hc t → HS9.WPointConcl M Q Z B t

@[expose] def Sec97SixWStatement : Prop :=
  Stroth95Statement → Sec4Statement → Sec97OneStatement → Sec57WStatement → Sec96WStatement →
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y → HS9.Sec4Concl M Q Z B X Y →
      HS9.OneConcl hc X Y → HS9.FourConcl M Q B Y → HS9.FiveConcl M Q Z B Y →
      HS9.SixConcl M Q B Y

structure Sec97RouteW : Prop where
  sec4 : Sec4Statement
  nine6w : Sec96WStatement
  five7w : Sec57WStatement
  one : Sec97OneStatement
  two : Sec97TwoStatement
  three : Sec97ThreeStatement
  four : Sec97FourStatement
  five : Sec97FiveStatement
  six : Sec97SixWStatement
  conn : Sec97ConnStatement
  fin : Sec98EndStatement

theorem stroth98Statement_of_routeW (h34 : Stroth34Statement) (h91 : Stroth91Statement)
    (h311a : Stroth311aStatement) (h92 : Stroth92Statement) (h93 : Stroth93Statement)
    (h94 : Stroth94Statement) (hConjV : Step94ConjVStatement) (hA : Sec9AExistsStatement)
    (hn5 : Sec9NGeFiveStatement) (hcore : Step95CoreStatement) (S : Sec97RouteW) :
    Stroth98Statement := by
  intro G _ _ M Q Z B hc n hw hn hno hgen hlarge t ht htQ hplus
  have hs : Sec9Hyp hc n t := ⟨⟨hw, hn, hno, hgen, ht, htQ⟩, hplus, hlarge⟩
  have h95 : Stroth95Statement :=
    stroth95_of_n5_core h92 h93 hConjV hn5 (sec95N5_of h34 h91 hA) hcore
  obtain ⟨X, Y, hsplit⟩ := h95 G M Q Z B hc n t hs
  have h4 := S.sec4 G M Q Z B hc n t hs X Y hsplit
  have h1 := S.one G M Q Z B hc n t hs X Y hsplit h4
  have h2 := S.two G M Q Z B hc n t hs X Y hsplit h4 h1
  have h3 := S.three G M Q Z B hc n t hs X Y hsplit h4 h1 h2
  have h4' := S.four G M Q Z B hc n t hs X Y hsplit h4 h1 h2 h3
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  obtain ⟨Z0, hZ0⟩ := exists_isCentrePre (Q := Q) (hc.Q_le_Rt ht)
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have h94' := h94 G M Q Z B hc n t hs Z0 hZ0
  unfold StronglyClosedMod at h94'
  push Not at h94'
  obtain ⟨s, hs0, g, hg, hL, hZ⟩ := h94'
  have hn1 : g * s * g⁻¹ ∈ LB M Q B := (Subgroup.mem_inf.mp hL).1
  have hn2 : g * s * g⁻¹ ∈ hc.CN t := (Subgroup.mem_inf.mp hL).2
  set y := g * s * g⁻¹ with hy
  set nn := r * y * r⁻¹ with hnn
  have hnnL : nn ∈ LB M Q (conjSubgroup r B) := by
    rw [hc.LB_conj hrM, mem_conjSubgroup]
    have e : r⁻¹ * nn * r = y := by rw [hnn]; group
    rw [e]
    exact hn1
  have hnnN : nn ∈ hc.CN t := hc.CN_conj_mem ht hrR hn2
  have hnnZ : nn ∉ Z0 := by
    intro h
    have hnorm := hZ0.mem_normalizer
      (fun ρ hρ z hz => (Subgroup.mem_normalizer_iff.mp
        (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) z).mp hz) hrR
    exact hZ ((Subgroup.mem_normalizer_iff.mp hnorm y).mpr h)
  have hconj : ConjMod M Q s nn := by
    refine ⟨?_, r * g, M.mul_mem hrM hg, ?_⟩
    · exact M.mul_mem (M.mul_mem hrM (hc.LB_le_M hn1)) (M.inv_mem hrM)
    · have e : nn * (r * g * s * (r * g)⁻¹)⁻¹ = 1 := by rw [hnn, hy]; group
      rw [e]
      exact Q.one_mem
  have h5 := S.five G M Q Z B hc n t hs X Y hsplit h4 h1 r hr Z0 hZ0 s hs0 nn hconj
    ⟨hnnL, hnnN⟩ hnnZ
  have h6 := S.six h95 S.sec4 S.one S.five7w S.nine6w G M Q Z B hc n t hs X Y hsplit h4 h1 h4' h5
  have hall : HS9.GoodAll M Q B Y := fun m hm =>
    S.conn G M Q Z B hc n t hs (HS9.GoodPt M Q B Y) (HS9.goodPt_self M Q B Y) h6
      (conjSubgroup m B) ⟨m, hm, rfl⟩
  obtain ⟨y₀, hy₀, hy₀Q⟩ := HS9.exists_mem_LB_inf_Y_not_mem hc h4
  have hCN := S.fin G M Q Z B hc n t hs X Y hsplit h4 hall y₀ hy₀ hy₀Q
  have hle := HS9.card_CN_le_of_le_Y h34 h311a hs hsplit (Subgroup.mem_inf.mp hy₀).1 hy₀Q hCN
  exact absurd (hlarge y₀ (Subgroup.mem_inf.mp hy₀).1 hy₀Q) (not_lt.mpr hle)

end CFSG.RankThree.GF2n.Stroth80
