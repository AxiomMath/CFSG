module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C636a
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588B5a
public import CFSG.LocalAnalysis.UniquenessCase.UC6C626L2Gen
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C626Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

open CFSG.ABGLocalTools CFSG.Open CFSG.Blueprint Subgroup in
open CFSG.RankThree.PartOne (IsStronglyPEmbedded) in
theorem c626gen_of_lieModel (h620 : m.C620) (hL : LieModel ↥m.L .PSL 2 m.r 2) : m.C626gen := by
  classical
  intro p hp P hP hPne
  have hpp : p.Prime := (Dat.sig_prime _ hp).1
  have hp2 : p ≠ 2 := (Dat.sig_prime _ hp).2
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hpr : p ≠ m.r := fun h => m.hrσ (h ▸ hp)
  have hstrong : IsStronglyPEmbedded p m.M :=
    m.hk.sig1_sp _ (m.hσ1 hp)
  have hPle : P ≤ m.M ⊓ normalizer (m.Z : Set G) := hP.le
  have hPM : P ≤ m.M := hPle.trans inf_le_left
  have hPZ : P ≤ normalizer (m.Z : Set G) := hPle.trans inf_le_right
  have hPN : ∀ x ∈ P, x ∈ normalizer (m.L : Set G) := fun x hx =>
    m.normalizer_Z_le_normalizer_L (hPZ hx)
  have hPp : IsPGroup p P := hP.isPGroup
  have hcenL : Subgroup.center ↥m.L = ⊥ := by
    obtain ⟨F, _, _, e, -, -⟩ := CFSG.GH74.GLS.EvenSelP.exists_l2Field_of_lieModel' m.hr m.d.odd hL
    exact CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv (CFSG.GH74.GLS.IVK.toPSL e)
      (CFSG.GorensteinWalter.psl2_center_eq_bot _)
  have hcen : ∀ s ∈ m.L, (∀ l ∈ m.L, s * l = l * s) → s = 1 := by
    intro s hs hcomm
    have : (⟨s, hs⟩ : ↥m.L) ∈ Subgroup.center ↥m.L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcomm g g.2).symm
    rw [hcenL, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hS1 : m.A ⊓ m.L ≤ gammaL m.L m.r m.E := by
    have hQ0 : m.E ⊓ m.L ≠ ⊥ := m.E_inf_L_ne_bot h620
    have hQ0p : IsPGroup m.r (m.E ⊓ m.L : Subgroup G) :=
      (IsElemAbelian.isPGroup m.d.E_el).to_inf_left
    have hQ0rank : 1 ≤ CFSG.Open.pRank m.r (m.E ⊓ m.L : Subgroup G) := one_le_pRank_of_ne_bot m.hr hQ0p hQ0
    refine le_trans ?_ (le_iSup_of_le (m.E ⊓ m.L) (le_iSup_of_le inf_le_left
      (le_iSup_of_le hQ0rank le_rfl)))
    intro a ha
    refine ⟨ha.2, ?_⟩
    refine mem_normalizer_of_forward_uc6 fun q hq => ?_
    have hcomm : a * q = q * a := by
      have := m.isElemAbelian_A.1.is_comm.comm ⟨a, ha.1⟩ ⟨q, m.E_le_A hq.1⟩
      exact congrArg Subtype.val this
    have : a * q * a⁻¹ = q := by rw [hcomm]; group
    rw [this]
    exact hq
  have hgenL : ∀ l : G, l ∈ m.L → orderOf l = p →
      m.L ≤ (m.A ⊓ m.L) ⊔ (m.L ⊓ normalizer (zpowers l : Set G)) := by
    intro l hlL hlord
    obtain ⟨Pw, hPwsyl, hPweq⟩ := m.exists_l2_sylow h620 hL
    set l' : ↥m.L := ⟨l, hlL⟩ with hl'
    have hl'ord : orderOf l' = p := by
      rw [← hlord, ← Subgroup.orderOf_coe]
    have hgen := sup_normalizer_zpowers_eq_top_of_lieModel m.hr m.d.odd hL hpp hp2 hpr
      (Pw : Subgroup ↥m.L) hPwsyl hl'ord
    intro g hg
    have hg' : (⟨g, hg⟩ : ↥m.L) ∈ (Pw : Subgroup ↥m.L) ⊔ normalizer (zpowers l' : Set ↥m.L) := by
      rw [hgen]
      exact Subgroup.mem_top _
    have hmap : g ∈ ((Pw : Subgroup ↥m.L) ⊔ normalizer (zpowers l' : Set ↥m.L)).map m.L.subtype :=
      ⟨_, hg', rfl⟩
    rw [Subgroup.map_sup] at hmap
    have hle : (Pw : Subgroup ↥m.L).map m.L.subtype ⊔
        (normalizer (zpowers l' : Set ↥m.L)).map m.L.subtype ≤
        (m.A ⊓ m.L) ⊔ (m.L ⊓ normalizer (zpowers l : Set G)) := by
      refine sup_le_sup ?_ ?_
      · rw [← hPweq, Subgroup.subgroupOf_map_subtype]
        exact inf_le_left
      · rintro _ ⟨n, hn, rfl⟩
        refine ⟨n.2, mem_normalizer_of_forward_uc6 fun y hy => ?_⟩
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        have h1 : (n * l' ^ k * n⁻¹ : ↥m.L) ∈ zpowers l' :=
          (mem_normalizer_iff.1 hn (l' ^ k)).1 (Subgroup.zpow_mem_zpowers l' k)
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h1
        refine ⟨j, ?_⟩
        have := congrArg (Subtype.val : ↥m.L → G) hj
        simpa using this
    exact hle hmap
  by_cases hK : P ⊓ centralizer (m.L : Set G) = ⊥
  ·
    obtain ⟨⟨x, hxP⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hPne
    have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
    set αx : MulAut ↥m.L := Subgroup.normalizerMonoidHom m.L ⟨x, hPN x hxP⟩ with hαx
    have hαodd : Odd (orderOf αx) := by
      obtain ⟨k, hk⟩ := hPp ⟨x, hxP⟩
      have hk' : x ^ p ^ k = 1 := congrArg Subtype.val hk
      have h1 : orderOf αx ∣ orderOf x := by
        have := orderOf_map_dvd (Subgroup.normalizerMonoidHom m.L)
          (⟨x, hPN x hxP⟩ : ↥(normalizer (m.L : Set G)))
        rwa [Subgroup.orderOf_mk] at this
      have h2 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
      exact Odd.of_dvd_nat ((hpp.odd_of_ne_two hp2).pow) (h1.trans h2)
    obtain ⟨s, hs⟩ := CFSG.ComponentClassification.AutL2Facts.oddOuterInner_lieModel_sq m.hr ↥m.L hL
      αx hαodd
    have hsx : ∀ l ∈ m.L, x * l * x⁻¹ = (s : G) * l * (s : G)⁻¹ := by
      intro l hl
      have := congrArg (fun γ : MulAut ↥m.L => ((γ ⟨l, hl⟩ : ↥m.L) : G)) hs
      simpa [hαx, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] using this
    have hsS : (s : G) ∈ innerPart m.L P := mem_innerPart.2 ⟨s.2, x, hxP, hsx⟩
    have hs1 : (s : G) ≠ 1 := by
      intro h1
      apply hx1'
      have hxC : x ∈ P ⊓ centralizer (m.L : Set G) := by
        refine ⟨hxP, mem_centralizer_iff.2 fun l hl => ?_⟩
        have h3 := hsx l hl
        rw [h1] at h3
        have h4 : x * l = l * x := by
          calc x * l = (x * l * x⁻¹) * x := by group
            _ = l * x := by rw [h3]; group
        exact h4.symm
      rw [hK, Subgroup.mem_bot] at hxC
      exact hxC
    have hSM : innerPart m.L P ≤ m.M ⊓ normalizer (m.Z : Set G) := by
      intro t ht
      refine ⟨?_, (Subgroup.centralizer_le_normalizer (m.Z : Set G)) (m.L_le_H (mem_innerPart.1 ht).1)⟩
      obtain ⟨htL, y, hyP, hy⟩ := mem_innerPart.1 ht
      by_cases hy1 : y = 1
      · subst hy1
        have : t = 1 := by
          refine hcen t htL fun l hl => ?_
          have h3 := hy l hl
          simp only [one_mul, inv_one, mul_one] at h3
          have h4 : t * l * t⁻¹ = l := h3.symm
          calc t * l = (t * l * t⁻¹) * t := by group
            _ = l * t := by rw [h4]
        rw [this]
        exact m.M.one_mem
      · have hty : t * y = y * t := (innerPart_comm htL hy).2
        have hzy : zpowers y ≠ ⊥ := fun h => hy1 (Subgroup.zpowers_eq_bot.1 h)
        have hzp : IsPGroup p (zpowers y) := hPp.to_le (Subgroup.zpowers_le.2 hyP)
        have hzM : zpowers y ≤ m.M := Subgroup.zpowers_le.2 (hPM hyP)
        refine hstrong.normalizer_le hzy hzp hzM ?_
        refine mem_normalizer_of_forward_uc6 fun w hw => ?_
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
        have : t * y ^ k * t⁻¹ = y ^ k := by
          have hc : Commute t y := hty
          rw [(hc.zpow_right k).eq]
          group
        rw [this]
        exact Subgroup.zpow_mem_zpowers y k
    have hSp : IsPGroup p (innerPart m.L P) := innerPart_isPGroup hPp hcen
    have hnorm : P ≤ normalizer ((innerPart m.L P : Subgroup G) : Set G) := innerPart_normalized hPN
    have hT : IsPGroup p (P ⊔ innerPart m.L P : Subgroup G) := hPp.to_sup_of_normal_right' hSp hnorm
    have hTP : (P ⊔ innerPart m.L P : Subgroup G) = P :=
      hP.eq_of_le le_sup_left (sup_le hPle hSM) hT
    have hsP : (s : G) ∈ P := by
      have : (s : G) ∈ (P ⊔ innerPart m.L P : Subgroup G) := Subgroup.mem_sup_right hsS
      rwa [hTP] at this
    obtain ⟨k, hk⟩ := hSp ⟨(s : G), hsS⟩
    have hk' : (s : G) ^ p ^ k = 1 := congrArg Subtype.val hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hpp).1 (orderOf_dvd_of_pow_eq_one hk')
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hs1 (orderOf_eq_one_iff.1 (by simpa using hj))
    set l : G := (s : G) ^ p ^ (j - 1) with hl
    have hlord : orderOf l = p := by
      rw [hl, orderOf_pow_of_dvd (pow_ne_zero _ hpp.ne_zero)
        (by rw [hj]; exact pow_dvd_pow p (Nat.sub_le j 1)), hj, Nat.pow_div (Nat.sub_le j 1) hpp.pos]
      have : j - (j - 1) = 1 := by omega
      rw [this, pow_one]
    have hlL : l ∈ m.L := m.L.pow_mem s.2 _
    have hlP : l ∈ P := P.pow_mem hsP _
    have hQP : zpowers l ≤ P := Subgroup.zpowers_le.2 hlP
    have hQne : zpowers l ≠ ⊥ := fun h => by
      have := Subgroup.zpowers_eq_bot.1 h
      rw [this, orderOf_one] at hlord
      exact hpp.one_lt.ne hlord
    have hQrank : 1 ≤ CFSG.Open.pRank p (zpowers l : Subgroup G) :=
      one_le_pRank_of_ne_bot hpp (hPp.to_le hQP) hQne
    have hS2 : m.L ⊓ normalizer (zpowers l : Set G) ≤ gammaL m.L p P :=
      le_iSup_of_le (zpowers l) (le_iSup_of_le hQP (le_iSup_of_le hQrank le_rfl))
    exact (hgenL l hlL hlord).trans (sup_le (hS1.trans le_sup_right) (hS2.trans le_sup_left))
  ·
    have hK1 : 1 ≤ CFSG.Open.pRank p (P ⊓ centralizer (m.L : Set G) : Subgroup G) :=
      one_le_pRank_of_ne_bot hpp (hPp.to_inf_left) hK
    have hL1 : m.L ≤ gammaL m.L p P := by
      refine le_trans ?_ (le_iSup_of_le (P ⊓ centralizer (m.L : Set G)) (le_iSup_of_le inf_le_left
        (le_iSup_of_le hK1 le_rfl)))
      intro l hl
      refine ⟨hl, mem_normalizer_of_forward_uc6 fun k hk => ?_⟩
      have hkc : k * l = l * k := (mem_centralizer_iff.1 hk.2 l hl).symm
      have : l * k * l⁻¹ = k := by rw [← hkc]; group
      rw [this]
      exact hk
    exact hL1.trans le_sup_left

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
