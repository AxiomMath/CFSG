module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailTILocal
public import CFSG.RankThree.GF2n.Tim79Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75

theorem NormIn_top_eq {X : Type*} [Group X] (V : Subgroup X) :
    NormIn ⊤ V = normalizer (V : Set X) :=
  top_inf_eq _

namespace TIConfig

theorem normalizer_comap_iff {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    {f : Y →* X} {V : Subgroup X} (hV : V ≤ f.range) (k : Y) :
    k ∈ normalizer ((V.comap f : Subgroup Y) : Set Y) ↔ f k ∈ normalizer (V : Set X) := by
  constructor
  · intro hk
    refine mem_normalizer_of_conj_mem fun z hz => ?_
    obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp (hV hz)
    have hw : k * w * k⁻¹ ∈ V.comap f :=
      conj_mem_of_mem_normalizer hk (Subgroup.mem_comap.mpr hz)
    have hw' := Subgroup.mem_comap.mp hw
    rwa [map_mul, map_mul, map_inv] at hw'
  · intro hk
    refine mem_normalizer_of_conj_mem fun w hw => ?_
    rw [Subgroup.mem_comap] at hw ⊢
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_of_mem_normalizer hk hw

theorem comap {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y] {H V N : Subgroup X}
    (h : TIConfig H V N) (f : Y →* X) (hf : Function.Injective f) (hH : f.range = H) :
    TIConfig ⊤ (V.comap f) (N.comap f) := by
  have hVr : V ≤ f.range := by
    rw [hH]
    exact h.V_le
  have hNr : N ≤ f.range := by
    rw [hH]
    intro n hn
    exact (mem_NormIn.1 (h.N_le hn)).1
  have hmemH : ∀ y : Y, f y ∈ H := fun y => by
    rw [← hH]
    exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
  have hsurjH : ∀ x ∈ H, ∃ y, f y = x := fun x hx => by
    rw [← hH] at hx
    exact MonoidHom.mem_range.mp hx
  refine ⟨le_top, ?_, h.V_pgroup.comap_of_injective f hf, ?_, ?_, ?_, ?_,
    h.N_pgroup.comap_of_injective f hf, ?_, ?_, ?_, ?_⟩
  · intro hbot
    apply h.V_ne_bot
    refine (Subgroup.eq_bot_iff_forall _).mpr fun v hv => ?_
    obtain ⟨y, rfl⟩ := hsurjH v (h.V_le hv)
    have hy : y ∈ V.comap f := Subgroup.mem_comap.mpr hv
    rw [hbot, Subgroup.mem_bot] at hy
    rw [hy, map_one]
  · intro x hx y hy
    apply hf
    rw [map_mul, map_mul]
    exact h.V_comm _ (Subgroup.mem_comap.mp hx) _ (Subgroup.mem_comap.mp hy)
  · intro g x hx hx1 hgx
    have hfx : f x ∈ V := Subgroup.mem_comap.mp hx
    have hfx1 : f x ≠ 1 := fun h1 => hx1 (hf (h1.trans (map_one f).symm))
    have hgx' : f g * f x * (f g)⁻¹ ∈ V := by
      have hc := Subgroup.mem_comap.mp hgx
      rwa [map_mul, map_mul, map_inv] at hc
    exact (normalizer_comap_iff hVr g).mpr (h.ti (f g) (f x) hfx hfx1 hgx')
  · intro n hn
    have hfn : f n ∈ N := Subgroup.mem_comap.mp hn
    exact mem_NormIn.2 ⟨Subgroup.mem_top n,
      (normalizer_comap_iff hVr n).mpr (mem_NormIn.1 (h.N_le hfn)).2⟩
  · intro k hk
    have hkV : k ∈ normalizer ((V.comap f : Subgroup Y) : Set Y) := (mem_NormIn.1 hk).2
    have hfk : f k ∈ NormIn H V :=
      mem_NormIn.2 ⟨hmemH k, (normalizer_comap_iff hVr k).mp hkV⟩
    exact (normalizer_comap_iff hNr k).mpr (h.N_normal (f k) hfk)
  · intro P hPK hPn hP
    have hP1 : P.map f ≤ NormIn H V := by
      rintro _ ⟨p, hp, rfl⟩
      exact mem_NormIn.2 ⟨hmemH p, (normalizer_comap_iff hVr p).mp (mem_NormIn.1 (hPK hp)).2⟩
    have hP1n : ∀ k ∈ NormIn H V, k ∈ normalizer ((P.map f : Subgroup X) : Set X) := by
      intro k hk
      obtain ⟨y, rfl⟩ := hsurjH k (mem_NormIn.1 hk).1
      have hyK : y ∈ NormIn ⊤ (V.comap f) :=
        mem_NormIn.2 ⟨Subgroup.mem_top y, (normalizer_comap_iff hVr y).mpr (mem_NormIn.1 hk).2⟩
      refine mem_normalizer_of_conj_mem fun z hz => ?_
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hz
      refine Subgroup.mem_map.mpr ⟨y * p * y⁻¹, conj_mem_of_mem_normalizer (hPn y hyK) hp, ?_⟩
      rw [map_mul, map_mul, map_inv]
    have hle : P.map f ≤ N := h.pcore_le (P.map f) hP1 hP1n (hP.map f)
    intro p hp
    exact Subgroup.mem_comap.mpr (hle (Subgroup.mem_map_of_mem f hp))
  · intro k hk hkc
    have hkV : k ∈ normalizer ((V.comap f : Subgroup Y) : Set Y) := (mem_NormIn.1 hk).2
    have hfk : f k ∈ NormIn H V :=
      mem_NormIn.2 ⟨hmemH k, (normalizer_comap_iff hVr k).mp hkV⟩
    refine Subgroup.mem_comap.mpr (h.cent_le (f k) hfk fun n hn => ?_)
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (hNr hn)
    have hmN : m ∈ N.comap f := Subgroup.mem_comap.mpr (by rw [hm]; exact hn)
    have hc := congrArg f (hkc m hmN)
    rw [map_mul, map_mul, hm] at hc
    exact hc
  · intro x hx n hn
    apply hf
    rw [map_mul, map_mul]
    exact h.VN_comm _ (Subgroup.mem_comap.mp hx) _ (Subgroup.mem_comap.mp hn)
  · intro A hVA hAK hAn hAab
    have hVA1 : V ≤ A.map f := by
      intro v hv
      obtain ⟨y, rfl⟩ := hsurjH v (h.V_le hv)
      exact Subgroup.mem_map.mpr ⟨y, hVA (Subgroup.mem_comap.mpr hv), rfl⟩
    have hA1K : A.map f ≤ NormIn H V := by
      rintro _ ⟨a, ha, rfl⟩
      exact mem_NormIn.2 ⟨hmemH a, (normalizer_comap_iff hVr a).mp (mem_NormIn.1 (hAK ha)).2⟩
    have hA1n : ∀ k ∈ NormIn H V, k ∈ normalizer ((A.map f : Subgroup X) : Set X) := by
      intro k hk
      obtain ⟨y, rfl⟩ := hsurjH k (mem_NormIn.1 hk).1
      have hyK : y ∈ NormIn ⊤ (V.comap f) :=
        mem_NormIn.2 ⟨Subgroup.mem_top y, (normalizer_comap_iff hVr y).mpr (mem_NormIn.1 hk).2⟩
      refine mem_normalizer_of_conj_mem fun z hz => ?_
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hz
      refine Subgroup.mem_map.mpr ⟨y * a * y⁻¹, conj_mem_of_mem_normalizer (hAn y hyK) ha, ?_⟩
      rw [map_mul, map_mul, map_inv]
    have hA1ab : ∀ x ∈ A.map f, ∀ y ∈ A.map f, x * y = y * x := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hAab a ha b hb]
    have hA1 : A.map f = V := h.maxAb (A.map f) hVA1 hA1K hA1n hA1ab
    ext a
    constructor
    · intro ha
      have hfa : f a ∈ V := by
        rw [← hA1]
        exact Subgroup.mem_map_of_mem f ha
      exact Subgroup.mem_comap.mpr hfa
    · intro ha
      exact hVA ha

end TIConfig

theorem hyp79_of_tiConfig {Y : Type} [Group Y] [Finite Y] {V N : Subgroup Y}
    (h : TIConfig ⊤ V N) (hq4 : 4 ≤ Nat.card V) (hsq : ∀ x ∈ V, x ^ 2 = 1) (hne : N ≠ V)
    (hgen : N = ⨆ (g : Y) (_ : conjSubgroup g V ≤ N), conjSubgroup g V)
    (hfit : generalizedFitting ↥(normalizer (V : Set Y)) = pCore 2 ↥(normalizer (V : Set Y))) :
    Tim79.Hyp79 (normalizer (V : Set Y)) V N := by
  have hVK : V ≤ normalizer (V : Set Y) := Subgroup.le_normalizer
  have hmaxLocal : IsMaximalTwoLocal (normalizer (V : Set Y)) := by
    refine ⟨⟨V, h.V_ne_bot, h.V_pgroup, rfl⟩, ?_⟩
    rintro H' hlt ⟨D, hD1, hDp, rfl⟩
    have hKD : NormIn ⊤ V ≤ NormIn ⊤ D := by
      rw [NormIn_top_eq, NormIn_top_eq]
      exact hlt.1
    have hle := h.maximal_local le_top hD1 hDp hKD
    refine hlt.2 ?_
    intro x hx
    exact (mem_NormIn.1 (hle (mem_NormIn.2 ⟨Subgroup.mem_top x, hx⟩))).2
  have hmaxAb : Maximal (fun U : Subgroup Y => U ≤ normalizer (V : Set Y) ∧
      normalizer (V : Set Y) ≤ normalizer (U : Set Y) ∧ IsMulCommutative U) V := by
    refine ⟨⟨hVK, le_rfl, ⟨⟨fun a b => Subtype.ext (h.V_comm _ a.2 _ b.2)⟩⟩⟩, ?_⟩
    rintro U ⟨hUK, hKU, hUab⟩ hVU
    have hUK' : U ≤ NormIn ⊤ V := by
      intro x hx
      exact mem_NormIn.2 ⟨Subgroup.mem_top x, hUK hx⟩
    have hKU' : ∀ k ∈ NormIn ⊤ V, k ∈ normalizer (U : Set Y) := by
      intro k hk
      exact hKU (mem_NormIn.1 hk).2
    have hUcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := by
      intro x hx y hy
      have hc := hUab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
      exact congrArg Subtype.val hc
    exact (h.maxAb U hVU hUK' hKU' hUcomm).le
  have hti : IsTI V := by
    intro g
    by_cases hbot : V ⊓ conjSubgroup g V = ⊥
    · exact Or.inl hbot
    · refine Or.inr ?_
      obtain ⟨x, hx, hx1⟩ : ∃ x ∈ V ⊓ conjSubgroup g V, x ≠ 1 := by
        by_contra hcon
        refine hbot ((Subgroup.eq_bot_iff_forall _).2 fun y hy => ?_)
        by_contra hy1
        exact hcon ⟨y, hy, hy1⟩
      obtain ⟨hxV, hxg⟩ := Subgroup.mem_inf.1 hx
      have hgx : g⁻¹ * x * g⁻¹⁻¹ ∈ V := by
        rw [inv_inv]
        exact mem_conjSubgroup.1 hxg
      have hginv : g⁻¹ ∈ normalizer (V : Set Y) := h.ti g⁻¹ x hxV hx1 hgx
      have hconj : conjSubgroup g V = V := by
        ext y
        rw [mem_conjSubgroup]
        have key := Subgroup.mem_normalizer_iff.mp hginv y
        rw [inv_inv] at key
        exact key.symm
      rw [hconj, inf_idem]
  have hPK : inSubgroup (pCore 2) (normalizer (V : Set Y)) ≤ NormIn ⊤ V := by
    rw [NormIn_top_eq]
    intro x hx
    obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact k.2
  have hPn : ∀ k ∈ NormIn ⊤ V,
      k ∈ normalizer ((inSubgroup (pCore 2) (normalizer (V : Set Y)) : Subgroup Y) : Set Y) := by
    intro k hk
    have hkK : k ∈ normalizer (V : Set Y) := (mem_NormIn.1 hk).2
    refine TIConfig.mem_normalizer_of_conj_mem fun z hz => ?_
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hz
    refine Subgroup.mem_map.mpr ⟨⟨k, hkK⟩ * c * (⟨k, hkK⟩ : ↥(normalizer (V : Set Y)))⁻¹, ?_, ?_⟩
    · exact (CFSG.pCore_normal (p := 2) (G := ↥(normalizer (V : Set Y)))).conj_mem c hc _
    · simp
  have hPp : IsPGroup 2 (inSubgroup (pCore 2) (normalizer (V : Set Y))) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(normalizer (V : Set Y)))).map
      (normalizer (V : Set Y)).subtype
  have hQ : N = inSubgroup (pCore 2) (normalizer (V : Set Y)) := by
    refine le_antisymm ?_ (h.pcore_le _ hPK hPn hPp)
    intro n hn
    have hnK : n ∈ normalizer (V : Set Y) := (mem_NormIn.1 (h.N_le hn)).2
    have hnorm : (N.comap (normalizer (V : Set Y)).subtype).Normal := by
      refine ⟨fun x hx g => ?_⟩
      have hx' : (x : Y) ∈ N := hx
      have hg : (g : Y) ∈ NormIn ⊤ V := mem_NormIn.2 ⟨Subgroup.mem_top _, g.2⟩
      have hc : (g : Y) * (x : Y) * (g : Y)⁻¹ ∈ N :=
        TIConfig.conj_mem_of_mem_normalizer (h.N_normal (g : Y) hg) hx'
      exact hc
    have hsub : N.comap (normalizer (V : Set Y)).subtype ≤ pCore 2 (normalizer (V : Set Y)) := by
      unfold pCore
      exact le_sSup ⟨hnorm, h.N_pgroup.comap_subtype⟩
    have hmem : (⟨n, hnK⟩ : ↥(normalizer (V : Set Y))) ∈ pCore 2 (normalizer (V : Set Y)) :=
      hsub (show (⟨n, hnK⟩ : ↥(normalizer (V : Set Y))) ∈
        N.comap (normalizer (V : Set Y)).subtype from hn)
    exact Subgroup.mem_map.mpr ⟨⟨n, hnK⟩, hmem, rfl⟩
  exact ⟨hmaxLocal, hfit, hmaxAb, hsq, hti, hq4, hQ, hgen, hne⟩

end CFSG.RankThree.GF2n.Stroth80
