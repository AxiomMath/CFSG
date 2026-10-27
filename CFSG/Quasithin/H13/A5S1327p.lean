module

public import CFSG.Quasithin.H13.A5S1327o
public import CFSG.Quasithin.H13.A5S1327l
public import CFSG.Quasithin.H13.A5S1327m

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem centralizer_UH_le_pCoreOf_two (h331 : Stmt3_3_1)
    (h1222 : Stmt12_2_2) (h5172 : Stmt5_1_7_two) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : ¬ Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3))) :
    H ⊓ Subgroup.centralizer (S.UH H : Set G) ≤ pCoreOf 2 H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hM
  have h501 := S.hyp501
  have hTH : T ≤ H := hH.1.1
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  obtain ⟨hMP, -⟩ := h501.minParabolic_of_isHStar h331 hH
  have hF : CharTwo H := S.charTwo_of_inH hH.1
  obtain ⟨hUO, hUel, hUred⟩ : S.UH H ≤ pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ∧
      IsElemAbelian 2 (S.UH H) ∧ IsTwoReducedIn H (S.UH H) :=
    conjClosure_isTwoReducedIn_of_charTwo hsyl hF le_rfl
  have hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H ≤ 2 := by
    obtain ⟨-, hq⟩ := isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian hH.1
    intro p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    have h1 := hq p hp hp2
    rwa [← pRank_top_subtype]
  have hJT := S.thompsonJ_not_le_centralizer_UH h331 h5172 hH hHZ
  set U := S.UH H with hUdef
  set J := H ⊓ Subgroup.centralizer (U : Set G) with hJ
  set K := kerIn (H ⊓ M) H with hK
  have hHN : H ≤ Subgroup.normalizer (U : Set G) := hUred.2.1
  have hZU : quasithinOmegaOneCenter T ≤ U := le_conjClosure _ _
  have hHU : ¬ H ≤ Subgroup.centralizer (U : Set G) :=
    fun h => hHZ (h.trans (Subgroup.centralizer_le hZU))
  have hHJ : H ≤ Subgroup.normalizer (J : Set G) := fun h hh =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hh, B6.le_normalizer_centralizer hHN hh⟩
  have hO2T : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsyl
  have hO2U : pCoreOf 2 H ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.le_centralizer_iff.mp (hUO.trans inf_le_right)
  have hHO : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  obtain ⟨K₁, K₂, B⟩ := exists_twoBlocks hUel hMP hsolv hSQT hUred hJT hS3
  obtain ⟨y₁, hy₁, hy₁3, hy₁1⟩ := S1417.exists_orderThree B.nat₁
  obtain ⟨t, htT, ht⟩ := B.swap
  have hy₂ : t * y₁ * t⁻¹ ∈ K₂ := by
    rw [← ht, B1.mem_conjAut]
    simpa [mul_assoc] using hy₁
  have hy₂3 : (t * y₁ * t⁻¹) ^ 3 = 1 := by rw [conj_pow, hy₁3]; group
  have hy₂1 : t * y₁ * t⁻¹ ≠ 1 := fun h => hy₁1 (by
    have e : y₁ = t⁻¹ * (t * y₁ * t⁻¹) * t := by group
    rw [e, h]; group)
  obtain ⟨-, hsylJ⟩ := E2_3_two_sylow_of_isSolvable hUel hMP hsolv hSQT hUred hJT
  obtain ⟨s, hsT, hsK, hs2, hs1⟩ := B.exists_inv_mem_K1 hsylJ
  have hcard9 := B.card_autI_twoResidual hy₁ hy₁3 hy₁1 hy₂ hy₂3 hy₂1
  obtain ⟨hLcomm, hLcube⟩ := B.autI_twoResidual_comm_cube hy₁ hy₁3 hy₁1 hy₂ hy₂3 hy₂1
  have hmemJ : ∀ (g : G) (hg : g ∈ H), convI hUel ⟨g, hHN hg⟩ = 1 → g ∈ J := fun g hg h1 =>
    ⟨hg, (convI_eq_one_iff hUel _).1 h1⟩
  have hconvJ : ∀ (g : G) (hg : g ∈ J), convI hUel ⟨g, hHN hg.1⟩ = 1 := fun g hg =>
    (convI_eq_one_iff hUel _).2 hg.2
  have hJK : J ≤ K := hMP.inf_centralizer_le_kerIn hUred hHU
  have hKH : K ≤ H := hMP.kerIn_le_H
  have hKJ : K ≤ J := by
    have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_kerIn (H ⊓ M) H
    have hKsH : autI hUel K ≤ autI hUel H := autI_mono hUel hKH
    have hTY : autI hUel T ≤ Subgroup.normalizer
        ((autI hUel K ⊓ autI hUel (twoResidual H) : Subgroup _) : Set _) :=
      fun φ hφ => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨autI_le_normalizer hUel (hTH.trans hHK) hφ,
          autI_le_normalizer hUel (hTH.trans (le_normalizer_twoResidual H)) hφ⟩
    by_cases hY : autI hUel K ⊓ autI hUel (twoResidual H) = ⊥
    ·
      have hK2 : IsPGroup 2 ↥(autI hUel K) := by
        intro φ
        obtain ⟨g, hgK, hg⟩ := (mem_autI hUel).1 φ.2
        obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient H g (hKH hgK)
        refine ⟨k, Subtype.ext ?_⟩
        have h1 : φ.1 ^ 2 ^ k ∈ autI hUel K ⊓ autI hUel (twoResidual H) :=
          ⟨(autI hUel K).pow_mem φ.2 _, by
            rw [← hg, ← map_pow]
            exact convI_mem_autI hUel hk _⟩
        rw [hY, Subgroup.mem_bot] at h1
        simpa using h1
      have hKn : ((autI hUel K).subgroupOf (autI hUel H)).Normal := by
        refine ⟨fun x hx h => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        exact (Subgroup.mem_normalizer_iff.mp (autI_le_normalizer hUel hHK h.2) x).mp hx
      have hbot := B2F.eq_bot_of_normal_isPGroup hUel hUred hKsH hKn hK2
      intro k hk
      exact ⟨hKH hk, (autI_eq_bot_iff hUel (hKH.trans hHN)).1 hbot hk⟩
    ·
      exfalso
      have hYeq := B.eq_of_normalized hy₁ hy₁3 hy₁1 hy₂ hy₂3 hy₂1 hsT hsK hs2 hs1 htT ht
        inf_le_right hY hTY
      have hLK : twoResidual H ≤ K := by
        intro g hg
        have hgH : g ∈ H := twoResidual_le H hg
        have h1 : convI hUel ⟨g, hHN hgH⟩ ∈ autI hUel K := by
          have : convI hUel ⟨g, hHN hgH⟩ ∈ autI hUel K ⊓ autI hUel (twoResidual H) := by
            rw [hYeq]
            exact convI_mem_autI hUel hg (hHN hgH)
          exact this.1
        obtain ⟨k, hkK, hk⟩ := (mem_autI hUel).1 h1
        have h2 : convI hUel (k⁻¹ * ⟨g, hHN hgH⟩) = 1 := by
          rw [map_mul, map_inv, hk, inv_mul_cancel]
        have h3 : (k : G)⁻¹ * g ∈ J :=
          ⟨H.mul_mem (H.inv_mem (hKH hkK)) hgH, (convI_eq_one_iff hUel _).1 h2⟩
        have := K.mul_mem hkK (hJK h3)
        simpa using this
      apply hH.2.1
      rw [eq_oTwoUpper_sup_of_isSylowTwoOf' hsyl, ← twoResidual_eq_oTwoUpper']
      exact sup_le (hLK.trans (kerIn_le.trans inf_le_right)) S.T_le_NL
  by_contra hcon
  set X := oTwoUpper J with hXdef
  have hXJ : X ≤ J := oTwoUpper_le J
  have hX1 : X ≠ ⊥ := by
    intro hX
    apply hcon
    refine le_pCoreOf_of_le_normalizer inf_le_left hHJ ?_
    intro j
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper J j.2
    rw [← hXdef, hX, Subgroup.mem_bot] at hk
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  by_cases hXCV : X ≤ Subgroup.centralizer (V : Set G)
  · exact S.false_of_oTwoUpper_le_centralizer_V h331 h1222 hH hHZ hX1 hXCV
  have hNJ := S.normalizer_thompsonJ_le_of_not_le h331 h1222 hH hHZ hXCV
  set R := pCoreOf 2 (X ⊔ T) with hRdef
  have hXH : X ≤ H := hXJ.trans inf_le_left
  have hHX : H ≤ Subgroup.normalizer (X : Set G) :=
    hHJ.trans (normalizer_le_normalizer_oTwoUpper J)
  have hsylXT : IsSylowTwoOf T (X ⊔ T) := isSylowTwoOf_of_le S.h13.sylow le_sup_right
  have hRT : R ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsylXT
  have hXTR : X ⊔ T ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pCoreOf 2 _
  have hO2R : pCoreOf 2 H ≤ R :=
    le_pCoreOf_of_le_normalizer (hO2T.trans le_sup_right) ((sup_le hXH hTH).trans hHO)
      (pCoreOf_isPGroup 2 H)
  have hO2X : pCoreOf 2 X ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer ((pCoreOf_le 2 X).trans hXH)
      (hHX.trans (normalizer_le_normalizer_pCoreOf 2 X)) (pCoreOf_isPGroup 2 X)
  obtain ⟨p₀, hp₀, hp₀2, hpow₀⟩ := exists_prime_pow_mem_of_mem_kerIn hMP hsolv
  have hRK : ∀ r ∈ R, ∀ k ∈ K, r * k * r⁻¹ * k⁻¹ ∈ pCoreOf 2 H := by
    intro r hr k hk
    obtain ⟨n, hn⟩ := hpow₀ k hk
    obtain ⟨x, hx, hxk⟩ := exists_mem_oTwoUpper_inv_mul_mem (hKJ hk)
      (hp₀.odd_of_ne_two hp₀2).pow hn
    have hrH : r ∈ H := hTH (hRT hr)
    have hxH : x ∈ H := hXH hx
    have hrx : r * x * r⁻¹ * x⁻¹ ∈ pCoreOf 2 H := by
      refine hO2X (le_pCoreOf_of_le_normalizer (inf_le_right : R ⊓ X ≤ X) ?_
        ((pCoreOf_isPGroup 2 _).to_le inf_le_left) ⟨?_, ?_⟩)
      · intro x' hx'
        exact Subgroup.inf_normalizer_le_normalizer_inf
          ⟨hXTR (Subgroup.mem_sup_left hx'), Subgroup.le_normalizer hx'⟩
      · have e : r * x * r⁻¹ * x⁻¹ = r * (x * r⁻¹ * x⁻¹) := by group
        rw [e]
        exact R.mul_mem hr ((Subgroup.mem_normalizer_iff.mp (hXTR (Subgroup.mem_sup_left hx))
          r⁻¹).mp (R.inv_mem hr))
      · refine X.mul_mem ?_ (X.inv_mem hx)
        exact (Subgroup.mem_normalizer_iff.mp (hHX hrH) x).mp hx
    have e : r * k * r⁻¹ * k⁻¹ =
        (r * x * r⁻¹ * x⁻¹) * (x * (r * (x⁻¹ * k) * r⁻¹ * (x⁻¹ * k)⁻¹) * x⁻¹) := by group
    rw [e]
    refine (pCoreOf 2 H).mul_mem hrx ?_
    have hrs : r * (x⁻¹ * k) * r⁻¹ * (x⁻¹ * k)⁻¹ ∈ pCoreOf 2 H :=
      (pCoreOf 2 H).mul_mem ((Subgroup.mem_normalizer_iff.mp (hHO hrH) _).mp hxk)
        ((pCoreOf 2 H).inv_mem hxk)
    exact (Subgroup.mem_normalizer_iff.mp (hHO hxH) _).mp hrs
  have hJRO : thompsonJ R ≤ pCoreOf 2 H := by
    by_cases hRO : R ≤ pCoreOf 2 H
    · exact (thompsonJ_le_self R).trans hRO
    obtain ⟨r, hrR, hrO⟩ := Set.not_subset.mp hRO
    have hKO : ¬ K ≤ pCoreOf 2 H := by
      intro hle
      apply hX1
      refine eq_bot_iff.mpr ((Subgroup.closure_le _).mpr fun w hw => ?_)
      have hwO : w ∈ pCoreOf 2 H := hle (hJK hw.1)
      obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 H ⟨w, hwO⟩
      have hb' : w ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
      have hw1 : w = 1 := by
        have h1 : w ^ orderOf w = 1 := pow_orderOf_eq_one w
        exact eq_one_of_pow_coprime hb' h1
          (Nat.Coprime.pow_left b (Nat.coprime_two_left.mpr hw.2))
      rw [hw1]
      exact Subgroup.one_mem _
    obtain ⟨p, hp, hp2, hpow, hdet⟩ := plusTwo_of hMP hsolv hSQT (hRT hrR) hrO (hRK r hrR) hKO
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
    have hsq : ∀ z ∈ K, z * z ∈ pCoreOf 2 H → z ∈ pCoreOf 2 H := by
      intro z hz hz2
      have e : z = z ^ p * ((z * z) ^ m)⁻¹ := by
        rw [hm, ← sq, ← pow_mul, pow_succ, mul_comm 2 m]; group
      rw [e]
      exact (pCoreOf 2 H).mul_mem (hpow z hz) ((pCoreOf 2 H).inv_mem ((pCoreOf 2 H).pow_mem hz2 m))
    have hcommJ : ∀ u ∈ twoResidual H, ∀ v ∈ twoResidual H, u * v * u⁻¹ * v⁻¹ ∈ J := by
      intro u hu v hv
      have huH := twoResidual_le H hu
      have hvH := twoResidual_le H hv
      have h1 : convI hUel (⟨u, hHN huH⟩ * ⟨v, hHN hvH⟩ * (⟨u, hHN huH⟩)⁻¹ *
          (⟨v, hHN hvH⟩)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv,
          hLcomm _ (convI_mem_autI hUel hu (hHN huH)) _ (convI_mem_autI hUel hv (hHN hvH))]
        group
      exact hmemJ _ (H.mul_mem (H.mul_mem (H.mul_mem huH hvH) (H.inv_mem huH)) (H.inv_mem hvH)) h1
    have htypeI : ∀ a ∈ R, a * a = 1 →
        (∀ g ∈ twoResidual H, a * g * a⁻¹ * g⁻¹ ∈ J) → a ∈ pCoreOf 2 H := by
      intro a haR ha2 hag
      refine mem_pCoreOf_of_commutator_mem hMP hsolv (hRT haR) fun g hg => ?_
      have hzK : a * g * a⁻¹ * g⁻¹ ∈ K := hJK (hag g hg)
      have h1 := hRK a haR _ hzK
      have h2 : a * (a * g * a⁻¹ * g⁻¹) * a⁻¹ * (a * g * a⁻¹ * g⁻¹) = 1 := by
        calc a * (a * g * a⁻¹ * g⁻¹) * a⁻¹ * (a * g * a⁻¹ * g⁻¹) =
              (a * a) * g * (a * a)⁻¹ * g⁻¹ := by group
          _ = 1 := by rw [ha2]; group
      have h3 : (a * g * a⁻¹ * g⁻¹) * (a * g * a⁻¹ * g⁻¹) ∈ pCoreOf 2 H := by
        have e : a * (a * g * a⁻¹ * g⁻¹) * a⁻¹ = (a * g * a⁻¹ * g⁻¹)⁻¹ :=
          eq_inv_of_mul_eq_one_left h2
        rw [e] at h1
        have := (pCoreOf 2 H).inv_mem h1
        simpa using this
      exact hsq _ hzK h3
    have htypeII : ∀ a ∈ R, a * a = 1 → a ∉ pCoreOf 2 H →
        ∀ g ∈ twoResidual H, a * g * a⁻¹ * g ∈ J := by
      intro a haR ha2 haO g₂ hg₂
      by_contra hg₂J
      obtain ⟨g₁, hg₁, hg₁J⟩ : ∃ g₁ ∈ twoResidual H, a * g₁ * a⁻¹ * g₁⁻¹ ∉ J := by
        by_contra hne
        push Not at hne
        exact haO (htypeI a haR ha2 hne)
      have haH : a ∈ H := hTH (hRT haR)
      have haN : a ∈ Subgroup.normalizer (U : Set G) := hHN haH
      have hconjL : ∀ g ∈ twoResidual H, a * g * a⁻¹ ∈ twoResidual H := fun g hg =>
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual H haH) g).mp hg
      have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha2
      set x := g₂ * (a * g₂ * a⁻¹) with hxdef
      set y := g₁ * (a * g₁ * a⁻¹)⁻¹ with hydef
      have hx : x ∈ twoResidual H := (twoResidual H).mul_mem hg₂ (hconjL g₂ hg₂)
      have hy : y ∈ twoResidual H :=
        (twoResidual H).mul_mem hg₁ ((twoResidual H).inv_mem (hconjL g₁ hg₁))
      have hxH : x ∈ H := twoResidual_le H hx
      have hyH : y ∈ H := twoResidual_le H hy
      have hax : a * x * a⁻¹ * x⁻¹ ∈ J := by
        have e : a * x * a⁻¹ * x⁻¹ = (a * g₂ * a⁻¹) * g₂ * (a * g₂ * a⁻¹)⁻¹ * g₂⁻¹ := by
          rw [hxdef]
          calc a * (g₂ * (a * g₂ * a⁻¹)) * a⁻¹ * (g₂ * (a * g₂ * a⁻¹))⁻¹ =
                (a * g₂ * a⁻¹) * ((a * a) * g₂ * (a * a)⁻¹) * (a * g₂ * a⁻¹)⁻¹ * g₂⁻¹ := by
                  group
            _ = _ := by rw [ha2]; group
        rw [e]
        exact hcommJ _ (hconjL g₂ hg₂) _ hg₂
      have hay : a * y * a⁻¹ * y = 1 := by
        rw [hydef]
        calc a * (g₁ * (a * g₁ * a⁻¹)⁻¹) * a⁻¹ * (g₁ * (a * g₁ * a⁻¹)⁻¹) =
              a * g₁ * a⁻¹ * ((a * a) * g₁ * (a * a)⁻¹)⁻¹ * g₁ * (a * g₁ * a⁻¹)⁻¹ := by group
          _ = 1 := by rw [ha2]; group
      have hxJ : x ∉ J := by
        intro hxJ
        apply hg₂J
        have e : a * g₂ * a⁻¹ * g₂ = g₂⁻¹ * x * g₂⁻¹⁻¹ := by rw [hxdef]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hHJ (H.inv_mem (twoResidual_le H hg₂))) x).mp hxJ
      have hyJ : y ∉ J := by
        intro hyJ
        apply hg₁J
        have e : a * g₁ * a⁻¹ * g₁⁻¹ = y⁻¹ := by rw [hydef]; group
        rw [e]
        exact J.inv_mem hyJ
      set as := convI hUel ⟨a, haN⟩ with has
      set xs := convI hUel ⟨x, hHN hxH⟩ with hxs
      set ys := convI hUel ⟨y, hHN hyH⟩ with hys
      have hxsL : xs ∈ autI hUel (twoResidual H) := convI_mem_autI hUel hx (hHN hxH)
      have hysL : ys ∈ autI hUel (twoResidual H) := convI_mem_autI hUel hy (hHN hyH)
      have hxs1 : xs ≠ 1 := fun h => hxJ (hmemJ x hxH h)
      have hys1 : ys ≠ 1 := fun h => hyJ (hmemJ y hyH h)
      have haxs : as * xs * as⁻¹ = xs := by
        have h1 : convI hUel (⟨a, haN⟩ * ⟨x, hHN hxH⟩ * (⟨a, haN⟩)⁻¹ * (⟨x, hHN hxH⟩)⁻¹) = 1 :=
          hconvJ _ hax
        rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
        exact mul_inv_eq_one.mp h1
      have hays : as * ys * as⁻¹ = ys⁻¹ := by
        have h1 : convI hUel (⟨a, haN⟩ * ⟨y, hHN hyH⟩ * (⟨a, haN⟩)⁻¹ * ⟨y, hHN hyH⟩) = 1 := by
          have e : (⟨a, haN⟩ * ⟨y, hHN hyH⟩ * (⟨a, haN⟩)⁻¹ * ⟨y, hHN hyH⟩ :
              ↥(Subgroup.normalizer (U : Set G))) = 1 := Subtype.ext hay
          rw [e, map_one]
        rw [map_mul, map_mul, map_mul, map_inv] at h1
        exact eq_inv_of_mul_eq_one_left h1
      have hinf : Subgroup.zpowers xs ⊓ Subgroup.zpowers ys = ⊥ := by
        refine eq_bot_iff.mpr fun z hz => ?_
        obtain ⟨⟨i, rfl⟩, ⟨j, hj⟩⟩ := hz
        have hfix : as * xs ^ i * as⁻¹ = xs ^ i := by
          rw [← conj_zpow, haxs]
        have hinv : as * xs ^ i * as⁻¹ = (xs ^ i)⁻¹ := by
          simp only at hj
          rw [← hj, ← conj_zpow, hays, inv_zpow]
        have h2 : (xs ^ i) ^ 2 = 1 := by
          rw [sq]
          calc xs ^ i * xs ^ i = xs ^ i * (xs ^ i)⁻¹ := by rw [← hinv, hfix]
            _ = 1 := mul_inv_cancel _
        have h3 : (xs ^ i) ^ 3 = 1 := hLcube _ ((autI hUel (twoResidual H)).zpow_mem hxsL i)
        exact Subgroup.mem_bot.mpr (eq_one_of_pow_coprime h3 h2 (by norm_num))
      have hcomm' : ∀ u ∈ Subgroup.zpowers xs, ∀ v ∈ Subgroup.zpowers ys, u * v = v * u :=
        fun u hu v hv =>
          hLcomm u ((Subgroup.zpowers_le).2 hxsL hu) v ((Subgroup.zpowers_le).2 hysL hv)
      have hgenL : Subgroup.zpowers xs ⊔ Subgroup.zpowers ys = autI hUel (twoResidual H) := by
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        have h1 := B2F.card_sup_mul_card_inf_of_commute hcomm'
        rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers,
          orderOf_eq_prime (hLcube xs hxsL) hxs1, orderOf_eq_prime (hLcube ys hysL) hys1] at h1
        exact Subgroup.eq_of_le_of_card_ge (sup_le ((Subgroup.zpowers_le).2 hxsL)
          ((Subgroup.zpowers_le).2 hysL)) (by rw [hcard9, h1])
      refine hdet a x y haH hx hy (hRK a haR) (hJK hax) (hJK (hay ▸ J.one_mem)) fun g hg => ?_
      have hgH : g ∈ H := twoResidual_le H hg
      have hgL : convI hUel ⟨g, hHN hgH⟩ ∈ Subgroup.zpowers xs ⊔ Subgroup.zpowers ys := by
        rw [hgenL]
        exact convI_mem_autI hUel hg (hHN hgH)
      obtain ⟨u, hu, v, hv, huv⟩ := S1417.exists_mul_of_mem_sup_of_commute hcomm' hgL
      obtain ⟨i, rfl⟩ := hu
      obtain ⟨j, rfl⟩ := hv
      refine ⟨i, j, hJK (hmemJ _ (H.mul_mem (H.inv_mem (H.mul_mem (H.zpow_mem hxH i)
        (H.zpow_mem hyH j))) hgH) ?_)⟩
      have e : (⟨(x ^ i * y ^ j)⁻¹ * g, hHN (H.mul_mem (H.inv_mem (H.mul_mem (H.zpow_mem hxH i)
          (H.zpow_mem hyH j))) hgH)⟩ : ↥(Subgroup.normalizer (U : Set G))) =
          ((⟨x, hHN hxH⟩ : ↥(Subgroup.normalizer (U : Set G))) ^ i *
            (⟨y, hHN hyH⟩ : ↥(Subgroup.normalizer (U : Set G))) ^ j)⁻¹ * ⟨g, hHN hgH⟩ :=
        Subtype.ext (by simp)
      rw [e, map_mul, map_inv, map_mul, map_zpow, map_zpow, ← huv, ← hxs, ← hys]
      group
    have hinvOf : ∀ a : ↥(Subgroup.normalizer (U : Set G)), (a : G) ∈ R → (a : G) * a = 1 →
        (a : G) ∉ pCoreOf 2 H → ∀ φ ∈ autI hUel (twoResidual H),
        convI hUel a * φ * (convI hUel a)⁻¹ = φ⁻¹ := by
      intro a haR ha2 haO φ hφ
      obtain ⟨g, hg, rfl⟩ := (mem_autI hUel).1 hφ
      have h1 : convI hUel (a * g * a⁻¹ * g) = 1 := hconvJ _ (htypeII a haR ha2 haO g hg)
      rw [map_mul, map_mul, map_mul, map_inv] at h1
      exact eq_inv_of_mul_eq_one_left h1
    refine iSup₂_le fun A hA => ?_
    have hAR : A ≤ R := hA.1
    have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => by
      have := hA.2.1.2 a ha
      rwa [sq] at this
    have hAN : A ≤ Subgroup.normalizer (U : Set G) := hAR.trans (hRT.trans (hTH.trans hHN))
    have hAC : ∀ a ∈ A, a ∈ Subgroup.centralizer (U : Set G) → a ∈ pCoreOf 2 H := by
      intro a ha haC
      have haK : a ∈ K := hJK ⟨hTH (hRT (hAR ha)), haC⟩
      obtain ⟨n, hn⟩ := hpow₀ a haK
      have ha2' : a ^ 2 = 1 := by rw [sq]; exact hA2 a ha
      have hcop : Nat.Coprime 2 (p₀ ^ n) :=
        Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hp₀).mpr (Ne.symm hp₀2))
      have e : a = (a ^ p₀ ^ n) ^ (1 : ℕ) := by
        have hodd : Odd (p₀ ^ n) := (hp₀.odd_of_ne_two hp₀2).pow
        obtain ⟨c, hc⟩ := hodd
        rw [pow_one, hc, pow_succ, pow_mul, ha2', one_pow, one_mul]
      rw [e, pow_one]
      exact hn
    by_contra hAO
    obtain ⟨a₀, ha₀, ha₀O⟩ := Set.not_subset.mp hAO
    have hII₀ := htypeII a₀ (hAR ha₀) (hA2 a₀ ha₀) ha₀O
    set a₀s := convI hUel ⟨a₀, hAN ha₀⟩ with ha₀s
    have ha₀s2 : a₀s ^ 2 = 1 := by
      rw [ha₀s, ← map_pow]
      have : (⟨a₀, hAN ha₀⟩ : ↥(Subgroup.normalizer (U : Set G))) ^ 2 = 1 :=
        Subtype.ext (by simp [sq, hA2 a₀ ha₀])
      rw [this, map_one]
    have hinv₀ : ∀ φ ∈ autI hUel (twoResidual H), a₀s * φ * a₀s⁻¹ = φ⁻¹ := by
      intro φ hφ
      obtain ⟨g, hg, rfl⟩ := (mem_autI hUel).1 hφ
      have h1 : convI hUel (⟨a₀, hAN ha₀⟩ * g * (⟨a₀, hAN ha₀⟩)⁻¹ * g) = 1 := hconvJ _ (hII₀ g hg)
      rw [map_mul, map_mul, map_mul, map_inv] at h1
      exact eq_inv_of_mul_eq_one_left h1
    have hAs : autI hUel A ≤ Subgroup.zpowers a₀s := by
      intro φ hφ
      obtain ⟨a', ha', rfl⟩ := (mem_autI hUel).1 hφ
      by_cases haO : (a' : G) ∈ pCoreOf 2 H
      · rw [(convI_eq_one_iff hUel _).2 (hO2U haO)]
        exact Subgroup.one_mem _
      · have hII := htypeII a' (hAR ha') (hA2 a' ha') haO
        have hprod : (a' : G) * a₀ ∈ pCoreOf 2 H := by
          refine htypeI _ (R.mul_mem (hAR ha') (hAR ha₀)) ?_ fun g hg => ?_
          · have hc : (a' : G) * a₀ = a₀ * a' := hA.2.1.1.is_comm.comm ⟨_, ha'⟩ ⟨_, ha₀⟩ |>
              congrArg Subtype.val
            calc (a' : G) * a₀ * ((a' : G) * a₀) = (a' : G) * (a₀ * a') * a₀ := by group
              _ = (a' : G) * ((a' : G) * a₀) * a₀ := by rw [← hc]
              _ = ((a' : G) * a') * (a₀ * a₀) := by group
              _ = 1 := by rw [hA2 _ ha', hA2 _ ha₀, one_mul]
          · have hgH := twoResidual_le H hg
            have hmem : (a' : G) * a₀ * g * ((a' : G) * a₀)⁻¹ * g⁻¹ ∈ H :=
              H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (hTH (hRT (hAR ha')))
                (hTH (hRT (hAR ha₀)))) hgH) (H.inv_mem (H.mul_mem (hTH (hRT (hAR ha')))
                (hTH (hRT (hAR ha₀)))))) (H.inv_mem hgH)
            refine hmemJ _ hmem ?_
            have h1 := hinvOf a' (hAR ha') (hA2 _ ha') haO _ (convI_mem_autI hUel hg (hHN hgH))
            have h2 := hinv₀ _ (convI_mem_autI hUel hg (hHN hgH))
            show convI hUel (a' * ⟨a₀, hAN ha₀⟩ * ⟨g, hHN hgH⟩ * (a' * ⟨a₀, hAN ha₀⟩)⁻¹ *
              (⟨g, hHN hgH⟩)⁻¹) = 1
            rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_mul]
            calc convI hUel a' * a₀s * convI hUel ⟨g, hHN hgH⟩ * (convI hUel a' * a₀s)⁻¹ *
                  (convI hUel ⟨g, hHN hgH⟩)⁻¹ = convI hUel a' * (a₀s * convI hUel ⟨g, hHN hgH⟩ *
                  a₀s⁻¹) * (convI hUel a')⁻¹ * (convI hUel ⟨g, hHN hgH⟩)⁻¹ := by group
              _ = convI hUel a' * (convI hUel ⟨g, hHN hgH⟩)⁻¹ * (convI hUel a')⁻¹ *
                  (convI hUel ⟨g, hHN hgH⟩)⁻¹ := by rw [h2]
              _ = (convI hUel a' * convI hUel ⟨g, hHN hgH⟩ * (convI hUel a')⁻¹)⁻¹ *
                  (convI hUel ⟨g, hHN hgH⟩)⁻¹ := by group
              _ = 1 := by rw [h1]; group
        have h1 := (convI_eq_one_iff hUel ⟨(a' : G) * a₀, hAN (A.mul_mem ha' ha₀)⟩).2
          (hO2U hprod)
        have e : (⟨(a' : G) * a₀, hAN (A.mul_mem ha' ha₀)⟩ : ↥(Subgroup.normalizer (U : Set G))) =
            a' * ⟨a₀, hAN ha₀⟩ := rfl
        rw [e, map_mul] at h1
        rw [eq_inv_of_mul_eq_one_left h1]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
    have hcardA : Nat.card (autI hUel A) ≤ 2 := by
      calc Nat.card (autI hUel A) ≤ Nat.card (Subgroup.zpowers a₀s) := Subgroup.card_le_of_le hAs
        _ = orderOf a₀s := Nat.card_zpowers a₀s
        _ ≤ 2 := Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one ha₀s2)
    have hFF := card_mul_le_of_isMaxElemAbelian hUel (hUO.trans (inf_le_left.trans hO2R)) hA
    have hAsC := card_autI_mul_card_inf hUel hAN
    have hfix := card_fixV_autI hUel hAN
    have hpos : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (U : Set G)) := Nat.card_pos
    have h1 : Nat.card U ≤ Nat.card (autI hUel A) * Nat.card (fixV (autI hUel A)) := by
      rw [hfix]
      rw [← hAsC] at hFF
      have h2 : Nat.card U * Nat.card ↥(A ⊓ Subgroup.centralizer (U : Set G)) ≤
          (Nat.card (autI hUel A) * Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G))) *
            Nat.card ↥(A ⊓ Subgroup.centralizer (U : Set G)) := by
        calc _ ≤ _ := hFF
          _ = _ := by ring
      exact Nat.le_of_mul_le_mul_right h2 hpos
    have hy₁L : y₁ ∈ autI hUel (twoResidual H) := by
      rw [B.autI_twoResidual_eq hy₁ hy₁3 hy₁1 hy₂ hy₂3 hy₂1]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y₁)
    have hy₂L : t * y₁ * t⁻¹ ∈ autI hUel (twoResidual H) := by
      rw [B.autI_twoResidual_eq hy₁ hy₁3 hy₁1 hy₂ hy₂3 hy₂1]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have h2 := B.two_mul_card_lt hy₁ hy₁3 hy₁1 hy₂ hy₂3 hy₂1 ha₀s2 (hinv₀ y₁ hy₁L)
      (hinv₀ _ hy₂L) (S := fixV (autI hUel A))
      (fun w hw => hw a₀s (convI_mem_autI hUel ha₀ (hAN ha₀)))
    have h3 : Nat.card (IntMod U hUel) = Nat.card U := rfl
    have h4 : Nat.card (autI hUel A) * Nat.card (fixV (autI hUel A)) ≤
        2 * Nat.card (fixV (autI hUel A)) := Nat.mul_le_mul_right _ hcardA
    omega
  have hJeq : thompsonJ R = thompsonJ (pCoreOf 2 H) := thompsonJ_eq_of_le hJRO hO2R
  apply hH.2.1
  calc H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := hHO
    _ ≤ Subgroup.normalizer (thompsonJ (pCoreOf 2 H) : Set G) :=
      GammaExtra.normalizer_le_normalizer_thompsonJ _
    _ = Subgroup.normalizer (thompsonJ R : Set G) := by rw [hJeq]
    _ ≤ M := hNJ

theorem centralizer_UH_le_pCoreOf_all (h331 : Stmt3_3_1)
    (h1222 : Stmt12_2_2) (h5172 : Stmt5_1_7_two) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) :
    H ⊓ Subgroup.centralizer (S.UH H : Set G) ≤ pCoreOf 2 H := by
  by_cases hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3))
  · exact S.centralizer_UH_le_pCoreOf h331 h1222 hH hHZ hsolv hS3
  · exact S.centralizer_UH_le_pCoreOf_two h331 h1222 h5172 hH hHZ hsolv hS3

end Setting

end CFSG.Quasithin.H13.A5
