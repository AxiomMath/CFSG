module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K318Symp
import CFSG.CharacterTheory.Semidihedral.UnitaryDValueLocal
import CFSG.Quasithin.Vol2.Ch11SecA12Cop
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmComp

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K318

open Subgroup
open CFSG.RankThree.SubgroupLists (spForm)
open scoped Matrix

variable {L : Type} [Group L] [Finite L]

theorem exists_pow_neg_one {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    {ψ : L →* GL (Fin 2 ⊕ Fin 2) (ZMod q)} {F : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q))}
    (hFq : IsPGroup q F) {s : L} {f : GL (Fin 2 ⊕ Fin 2) (ZMod q)} (hf : f ∈ F)
    (hs : ψ s = -f) : ∃ m : ℕ, ψ (s ^ m) = -1 ∧ IsPGroup 2 (zpowers (s ^ m)) := by
  have hq : q.Prime := Fact.out
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos s).ne'
  have hpow : ψ (s ^ m) = -(f ^ m) := by rw [map_pow, hs, hm.neg_pow]
  have hord : orderOf (s ^ m) = 2 ^ k := by
    rw [orderOf_pow_of_dvd hm.pos.ne' (Dvd.intro_left _ hkm.symm), hkm,
      Nat.mul_div_cancel _ hm.pos]
  refine ⟨m, ?_, IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hord])⟩
  have h1 : (f ^ m) ^ (2 ^ (k + 1)) = 1 := by
    have h := congrArg ψ (pow_orderOf_eq_one (s ^ m))
    rw [hord, map_pow, hpow, map_one] at h
    have he : Even (2 ^ (k + 1)) := ⟨2 ^ k, by ring⟩
    rw [← he.neg_pow (f ^ m), show 2 ^ (k + 1) = 2 ^ k * 2 by ring, pow_mul, h, one_pow]
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.1 hFq ⟨f ^ m, pow_mem hf m⟩
  have hdvd : q ^ n ∣ 2 ^ (k + 1) := by
    rw [← hn]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h1))
  have hcop : Nat.Coprime q 2 := (Nat.coprime_primes hq Nat.prime_two).2 hq2
  have hn1 : q ^ n = 1 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow n (k + 1) hcop) dvd_rfl hdvd
  have hfm : f ^ m = 1 := by
    have h2 : orderOf (⟨f ^ m, pow_mem hf m⟩ : F) = 1 := hn.trans hn1
    rw [orderOf_eq_one_iff] at h2
    exact congrArg Subtype.val h2
  rw [hpow, hfm]

theorem three_lt_pRank_of_flag {X : Subgroup L} {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    {ψ : L →* GL (Fin 2 ⊕ Fin 2) (ZMod q)} (hD : SympSection X q ψ)
    (hneg : (-1 : GL (Fin 2 ⊕ Fin 2) (ZMod q)) ∈ ψ.range)
    {F : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q))} (hFψ : F ≤ ψ.range) (hFq : IsPGroup q F)
    (hFc : ¬ IsCyclic F) {W : Submodule (ZMod q) (Fin 2 ⊕ Fin 2 → ZMod q)}
    (hW : Nat.card W = q ^ 2) (hWi : ∀ v ∈ W, ∀ w ∈ W, spForm 2 (ZMod q) v w = 0)
    (hFW : ∀ f ∈ F, ∀ w ∈ W, (f : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod q)) *ᵥ w = w) :
    3 < CFSG.Open.pRank q (⊤ : Subgroup L) := by
  classical
  have hq : q.Prime := Fact.out
  have hchar : ringChar (ZMod q) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hq2
  obtain ⟨D, hDn, -, hDexp, hD5, π, hπs, hπc, hπe, hπcomm⟩ := hD
  let M : Subgroup L := F.comap ψ
  obtain ⟨P⟩ : Nonempty (Sylow q M) := inferInstance
  let U : Subgroup L := (P : Subgroup M).map M.subtype
  have hUM : U ≤ M := map_subtype_le _
  have hUq : IsPGroup q U := P.isPGroup'.map M.subtype
  obtain ⟨t₀, ht₀⟩ := hneg
  have ht₀M : ∀ k ∈ M, t₀ * k * t₀⁻¹ ∈ M := by
    intro k hk
    rw [mem_comap] at hk ⊢
    rw [map_mul, map_mul, map_inv, ht₀]
    simpa using hk
  have hPU : (P : Subgroup M) = U.subgroupOf M := by
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  obtain ⟨a, haM, has⟩ :=
    CFSG.Semidihedral.UnitaryDValue.exists_mul_mem_normalizer_of_sylow hUM P hPU ht₀M
  have hψs : ψ (a * t₀) = -(ψ a) := by rw [map_mul, ht₀, mul_neg_one]
  obtain ⟨m, htψ, ht2⟩ := exists_pow_neg_one hq2 hFq (mem_comap.1 haM) hψs
  set t : L := (a * t₀) ^ m
  have htU : t ∈ normalizer (U : Set L) := pow_mem has m
  have hψtM : (ψ t : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod q)) = -1 := by
    rw [htψ, Units.val_neg, Units.val_one]
  have hUF : ∀ f ∈ F, ∃ b ∈ U, ψ b = f := by
    let ψM : M →* F := (ψ.comp M.subtype).codRestrict F fun x => x.2
    have hψM : Function.Surjective ψM := by
      rintro ⟨f, hf⟩
      obtain ⟨g, rfl⟩ := hFψ hf
      exact ⟨⟨g, hf⟩, rfl⟩
    have htop : (⊤ : Subgroup F) = ((P.mapSurjective hψM : Sylow q F) : Subgroup F) :=
      (P.mapSurjective hψM).is_maximal' (hFq.to_subgroup ⊤) le_top
    intro f hf
    have hmem : (⟨f, hf⟩ : F) ∈ ((P.mapSurjective hψM : Sylow q F) : Subgroup F) :=
      htop ▸ mem_top _
    rw [Sylow.coe_mapSurjective] at hmem
    obtain ⟨x, hxP, hx⟩ := hmem
    exact ⟨x, ⟨x, hxP, rfl⟩, congrArg Subtype.val hx⟩
  let Y : Subgroup L := U ⊓ centralizer (zpowers t : Set L)
  have hYU : Y ≤ U := inf_le_left
  have hYF : ∀ f ∈ F, ∃ y ∈ Y, ψ y = f := by
    intro f hf
    obtain ⟨b, hbU, rfl⟩ := hUF f hf
    have hA : zpowers t ≤ normalizer (U : Set L) := zpowers_le.2 htU
    have hBN : U ≤ normalizer ((U ⊓ ψ.ker : Subgroup L) : Set L) := by
      intro u hu
      rw [mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨U.mul_mem (U.mul_mem hu h1) (U.inv_mem hu), ψ.normal_ker.conj_mem h h2 u⟩
      · rintro ⟨h1, h2⟩
        have e : h = u⁻¹ * (u * h * u⁻¹) * u⁻¹⁻¹ := by group
        rw [e]
        exact ⟨U.mul_mem (U.mul_mem (U.inv_mem hu) h1) (U.inv_mem (U.inv_mem hu)),
          ψ.normal_ker.conj_mem _ h2 u⁻¹⟩
    have hcop : Nat.Coprime 2 (Nat.card (U ⊓ ψ.ker : Subgroup L)) := by
      obtain ⟨n, hn⟩ := (hUq.to_le inf_le_left).exists_card_eq
      rw [hn]
      exact Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2))
    have hc : ∀ x ∈ zpowers t, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ U ⊓ ψ.ker := by
      intro x hx y hy
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hx
      refine Subgroup.mem_inf.2
        ⟨U.mul_mem ((mem_normalizer_iff.1 (hA hx) y).1 hy) (U.inv_mem hy), ?_⟩
      rw [MonoidHom.mem_ker]
      have hcomm : Commute (ψ (t ^ n)) (ψ y) := by
        rw [map_zpow, htψ]
        exact (Commute.neg_one_left _).zpow_left n
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm.eq, mul_inv_cancel_right,
        mul_inv_cancel]
    obtain ⟨c, hcY, hcb⟩ := CFSG.Quasithin.Vol2.Ch11.SecA.exists_mem_centralizer_of_coprime
      Nat.prime_two ht2 hA inf_le_left hBN hcop hc hbU
    refine ⟨c, hcY, ?_⟩
    have h := (Subgroup.mem_inf.1 hcb).2
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h
    exact h
  have hYM : Y.map ψ = F := by
    refine le_antisymm ?_ fun f hf => ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hUM (hYU hy)
    · obtain ⟨y, hy, rfl⟩ := hYF f hf
      exact ⟨y, hy, rfl⟩
  have hYc : ¬ IsCyclic Y := by
    intro hcyc
    have h : IsCyclic (Y.map ψ) := isCyclic_of_surjective _ (ψ.subgroupMap_surjective Y)
    rw [hYM] at h
    exact hFc h
  obtain ⟨E, hEY, hEexp, hEcard⟩ :=
    CFSG.Goldschmidt.Sec8.exists_plane hq hq2 (hUq.to_le hYU) hYc
  have hcardV : Nat.card (Multiplicative (Fin 2 ⊕ Fin 2 → ZMod q)) = q ^ 4 := by
    change Nat.card (Fin 2 ⊕ Fin 2 → ZMod q) = q ^ 4
    simp [Nat.card_fun]
  have hcomap : ∀ H : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → ZMod q)),
      Nat.card (H.comap π) * q ^ 4 = q ^ 5 * Nat.card H := by
    intro H
    have h1 := (H.comap π).card_mul_index
    have h2 := H.card_mul_index
    rw [Subgroup.index_comap_of_surjective H hπs, hD5] at h1
    rw [hcardV] at h2
    rw [← h2, ← h1]
    ring
  have hK : Nat.card π.ker = q := by
    have h := hcomap ⊥
    rw [MonoidHom.comap_bot, Subgroup.card_bot] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hq.pos 4) (h.trans (by ring))
  let W' : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → ZMod q)) := W.toAddSubgroup.toSubgroup
  have hW'c : Nat.card W' = q ^ 2 := by
    rw [← hW]
    exact Nat.card_congr (Multiplicative.toAdd.subtypeEquiv fun _ => Iff.rfl)
  have hAc : Nat.card (W'.comap π) = q ^ 3 := by
    have h := hcomap W'
    rw [hW'c] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hq.pos 4) (h.trans (by ring))
  have hmemA : ∀ x : D, x ∈ W'.comap π ↔ Multiplicative.toAdd (π x) ∈ W := fun _ => Iff.rfl
  have hEK : ¬ E ≤ π.ker.map D.subtype := by
    intro hle
    have h := Subgroup.card_le_of_le hle
    rw [hEcard, card_map_of_injective D.subtype_injective, hK] at h
    nlinarith [hq.two_le]
  obtain ⟨y, hyE, hyK⟩ := SetLike.not_le_iff_exists.1 hEK
  have hyY : y ∈ Y := hEY hyE
  have hyt : t * y = y * t := mem_centralizer_iff.1 hyY.2 _ (mem_zpowers _)
  have hyq : y ^ q = 1 := by
    have h := congrArg Subtype.val (hEexp ⟨y, hyE⟩)
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
  have hψy : ψ y ∈ F := hUM (hYU hyY)
  have hyA : y ∉ (W'.comap π).map D.subtype := by
    rintro ⟨x, -, hx⟩
    have hx' : (x : L) = y := hx
    apply hyK
    refine Subgroup.mem_map.2 ⟨x, ?_, hx⟩
    have h := hπe t x x (by rw [hx', hyt, mul_inv_cancel_right])
    rw [hψtM, Matrix.neg_mulVec, Matrix.one_mulVec] at h
    have h0 : Multiplicative.toAdd (π x) = 0 := by
      funext i
      have hi := congrFun h i
      rw [Pi.neg_apply] at hi
      exact (Ring.eq_self_iff_eq_zero_of_char_ne_two hchar).1 hi
    rw [← toAdd_one] at h0
    exact MonoidHom.mem_ker.2 (Multiplicative.toAdd.injective h0)
  have hyc : ∀ e ∈ (W'.comap π).map D.subtype, e * y = y * e := by
    rintro _ ⟨x, hxA, rfl⟩
    have hxW : Multiplicative.toAdd (π x) ∈ W := (hmemA x).1 hxA
    obtain ⟨c₁, hc₁, r1⟩ : ∃ c₁ : D, π c₁ = 1 ∧ y * (x : L) * y⁻¹ = (c₁ : L) * x := by
      let x₁ : D := ⟨y * x * y⁻¹, hDn.conj_mem _ x.2 y⟩
      have h1 := hπe y x x₁ rfl
      rw [hFW _ hψy _ hxW] at h1
      refine ⟨x₁ * x⁻¹, ?_, ?_⟩
      · rw [map_mul, map_inv, ← Multiplicative.toAdd.injective h1, mul_inv_cancel]
      · rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
    obtain ⟨c₂, hc₂, r2⟩ : ∃ c₂ : D, π c₂ = 1 ∧ t * (x : L) * t⁻¹ = (c₂ : L) * (x : L)⁻¹ := by
      let x₂ : D := ⟨t * x * t⁻¹, hDn.conj_mem _ x.2 t⟩
      have h2 := hπe t x x₂ rfl
      rw [hψtM, Matrix.neg_mulVec, Matrix.one_mulVec] at h2
      have e2 : π x₂ = (π x)⁻¹ := Multiplicative.toAdd.injective (by rw [toAdd_inv, ← h2])
      refine ⟨x₂ * x, ?_, ?_⟩
      · rw [map_mul, e2, inv_mul_cancel]
      · rw [Subgroup.coe_mul, mul_inv_cancel_right]
    have hz₁ := hπc c₁ hc₁
    have hz₂ := hπc c₂ hc₂
    have key : (c₂ : L) * ((c₁ : L) * x)⁻¹ = (c₁ : L) * ((c₂ : L) * (x : L)⁻¹) := by
      have e : y * (t * x * t⁻¹) * y⁻¹ = t * (y * x * y⁻¹) * t⁻¹ := by
        calc y * (t * x * t⁻¹) * y⁻¹ = (y * t) * x * (y * t)⁻¹ := by group
          _ = (t * y) * x * (t * y)⁻¹ := by rw [hyt]
          _ = t * (y * x * y⁻¹) * t⁻¹ := by group
      rw [r1, r2] at e
      calc (c₂ : L) * ((c₁ : L) * x)⁻¹ = (c₂ * y) * ((x : L)⁻¹ * y⁻¹) := by
            rw [← r1]
            group
        _ = (y * c₂) * ((x : L)⁻¹ * y⁻¹) := by rw [hz₂ y]
        _ = y * ((c₂ : L) * (x : L)⁻¹) * y⁻¹ := by group
        _ = t * ((c₁ : L) * x) * t⁻¹ := e
        _ = (t * c₁) * ((x : L) * t⁻¹) := by group
        _ = (c₁ * t) * ((x : L) * t⁻¹) := by rw [hz₁ t]
        _ = (c₁ : L) * (t * x * t⁻¹) := by group
        _ = (c₁ : L) * ((c₂ : L) * (x : L)⁻¹) := by rw [r2]
    have hinv : (c₁ : L)⁻¹ = c₁ := by
      rw [← hz₁ ((c₂ : L) * (x : L)⁻¹)] at key
      have k2 : ((c₂ : L) * (x : L)⁻¹) * (c₁ : L)⁻¹ = ((c₂ : L) * (x : L)⁻¹) * c₁ := by
        rw [← key]
        group
      exact mul_left_cancel k2
    have hsq : (c₁ : L) * c₁ = 1 := by
      calc (c₁ : L) * c₁ = c₁ * (c₁ : L)⁻¹ := by rw [hinv]
        _ = 1 := mul_inv_cancel _
    have hc₁1 : (c₁ : L) = 1 := by
      obtain ⟨j, hj⟩ := hq.odd_of_ne_two hq2
      have h := hDexp _ c₁.2
      rw [hj, pow_succ, pow_mul, sq, hsq, one_pow, one_mul] at h
      exact h
    rw [hc₁1, one_mul, mul_inv_eq_iff_eq_mul] at r1
    exact r1.symm
  have hAc' : Nat.card ((W'.comap π).map D.subtype) = q ^ 3 := by
    rw [card_map_of_injective D.subtype_injective, hAc]
  have hAel : CFSG.Open.IsElemAbelian q ((W'.comap π).map D.subtype) := by
    refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨b₁, hb₁, rfl⟩⟩ := u
      obtain ⟨_, ⟨b₂, hb₂, rfl⟩⟩ := v
      apply Subtype.ext
      have h := (hπcomm b₁ b₂).2
        (hWi _ ((hmemA b₁).1 hb₁) _ ((hmemA b₂).1 hb₂))
      simpa using congrArg Subtype.val h
    · rintro _ ⟨b, -, rfl⟩
      exact hDexp _ b.2
  obtain ⟨hel, hcard⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm.isElemAbelian_card_sup_zpowers_of_card
      hq hAel hAc' hyq hyA hyc
  have h4 := CFSG.SectionRank.le_pRank hq.one_lt
    (le_top : (W'.comap π).map D.subtype ⊔ zpowers y ≤ ⊤) hel hcard
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.K318
