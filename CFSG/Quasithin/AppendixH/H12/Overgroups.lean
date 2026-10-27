module

public import CFSG.Quasithin.AppendixH.H12.OvergroupsLat
public import CFSG.Quasithin.AppendixH.H12.OvergroupsCover
public import CFSG.Quasithin.AppendixH.H12.Vocab

public section

namespace CFSG.Quasithin.AppendixH.H12

open CFSG.Quasithin CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
open CFSG.ASVolI.ChH (IsMaximalIn)

private theorem exists_conj_map_eq_of_sylow {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (P Q : Sylow p G) :
    ∃ g : G, (Q : Subgroup G) = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  exact ⟨g, by rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]; rfl⟩

private lemma isCoatom_subgroupOf_iff {G : Type*} [Group G] {L Y : Subgroup G} (hY : Y ≤ L) :
    IsCoatom (Y.subgroupOf L) ↔ IsMaximalIn Y L := by
  constructor
  · intro h
    refine ⟨lt_of_le_of_ne hY ?_, ?_⟩
    · intro hYL
      exact h.1 (by rw [hYL, Subgroup.subgroupOf_self])
    · intro Z hYZ hZL
      have hle : Y.subgroupOf L ≤ Z.subgroupOf L := Subgroup.comap_mono hYZ
      rcases eq_or_lt_of_le hle with heq | hlt
      · left
        rw [← Subgroup.map_subgroupOf_eq_of_le hY, ← Subgroup.map_subgroupOf_eq_of_le hZL, heq]
      · right
        have htop : Z.subgroupOf L = ⊤ := h.2 (Z.subgroupOf L) hlt
        rw [← Subgroup.map_subgroupOf_eq_of_le hZL, htop, ← Subgroup.subgroupOf_self L,
          Subgroup.map_subgroupOf_eq_of_le le_rfl]
  · intro h
    refine ⟨?_, ?_⟩
    · intro htop
      have hYL : Y = L := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hY, htop, ← Subgroup.subgroupOf_self L,
          Subgroup.map_subgroupOf_eq_of_le le_rfl]
      exact (ne_of_lt h.1) hYL
    · intro Z hlt
      have hYle : Y ≤ Z.map L.subtype := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hY]
        exact Subgroup.map_mono (le_of_lt hlt)
      have hZY : Z.map L.subtype ≤ L := Subgroup.map_subtype_le Z
      rcases h.2 (Z.map L.subtype) hYle hZY with hW | hW
      · exfalso
        have hZeq : Z = Y.subgroupOf L := by
          rw [← Subgroup.comap_map_eq_self_of_injective L.subtype_injective Z, hW,
            Subgroup.comap_subtype]
        exact (ne_of_gt hlt) hZeq
      · rw [← Subgroup.comap_map_eq_self_of_injective L.subtype_injective Z, hW,
          Subgroup.comap_subtype, Subgroup.subgroupOf_self]

private lemma subgroupOf_le_subgroupOf_iff {G : Type*} [Group G] {L T Y : Subgroup G}
    (hT : T ≤ L) (hY : Y ≤ L) : T.subgroupOf L ≤ Y.subgroupOf L ↔ T ≤ Y := by
  constructor
  · intro h
    rw [← Subgroup.map_subgroupOf_eq_of_le hT, ← Subgroup.map_subgroupOf_eq_of_le hY]
    exact Subgroup.map_mono h
  · intro h
    exact Subgroup.comap_mono h

theorem overgroups_of_isHat {Γ : Type} [Group Γ]
    {L T : Subgroup Γ} (hL : IsHat ↥L ↥CFSG.Blueprint.NativeSporadic.M22)
    (hT : IsSylowIn 2 T L) :
    ∃ M N : Subgroup Γ, M ≤ L ∧ N ≤ L ∧ T ≤ M ∧ T ≤ N ∧
      (Subgroup.center ↥L).map L.subtype ≤ M ∧ (Subgroup.center ↥L).map L.subtype ≤ N ∧
      Nat.card M = 17280 ∧ Nat.card N = 5760 ∧ IsMaximalIn M L ∧ IsMaximalIn N L ∧ M ≠ N ∧
      (∀ Y : Subgroup Γ, IsMaximalIn Y L → T ≤ Y → Y = M ∨ Y = N) ∧
      (∀ Y : Subgroup Γ, Y ≤ L → T ≤ Y → (Subgroup.center ↥L).map L.subtype ≤ Y →
        Nat.card Y = 17280 → Y = M) ∧
      (∀ Y : Subgroup Γ, Y ≤ L → T ≤ Y → (Subgroup.center ↥L).map L.subtype ≤ Y →
        Nat.card Y = 5760 → Y = N) := by
  classical
  obtain ⟨hQ, hZcard, hquot⟩ := hL
  obtain ⟨e⟩ := hquot
  have hperf : Group.IsPerfect ↥L := hQ.1
  have hMgrp : Nat.card ↥Mgrp = 443520 := cert.card_m (rawIsEnc 22)
      (LatCert.closedOK_of_check (cert_check)) (LatCert.sizesOK_of_check (cert_check))
  have hM22card : Nat.card ↥CFSG.Blueprint.NativeSporadic.M22 = 443520 := by
    rw [← mGens_closure]; exact hMgrp
  have hquotcard : Nat.card (↥L ⧸ Subgroup.center ↥L) = 443520 := by
    rw [Nat.card_congr e.toEquiv, hM22card]
  have hcardLg : Nat.card ↥L = 1330560 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
    rw [hquotcard, hZcard] at h
    omega
  haveI hfinL : Finite ↥L := (Nat.card_ne_zero.mp (by rw [hcardLg]; norm_num)).2
  have hcardT : Nat.card (T.subgroupOf L) = 128 := by
    have h := Sylow.card_eq_multiplicity hT.toSylow
    rw [IsSylowIn.coe_toSylow, hcardLg] at h
    have hfac : (1330560 : ℕ).factorization 2 = 7 := by
      have h' : (1330560 : ℕ) = 2 ^ 7 * 10395 := by norm_num
      rw [h', Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 10395), add_zero,
        Nat.factorization_pow, Nat.Prime.factorization Nat.prime_two]
      simp
    rw [hfac] at h
    norm_num at h ⊢
    exact h
  have hdisj : Subgroup.center ↥L ⊓ (T.subgroupOf L) = ⊥ := by
    apply Subgroup.inf_eq_bot_of_coprime
    rw [hZcard, hcardT]
    decide
  let φ : ↥CFSG.Blueprint.NativeSporadic.M22 ≃* ↥Mgrp :=
    (MulEquiv.subgroupCongr mGens_closure).symm
  let π₁ : ↥L →* ↥Mgrp :=
    φ.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L)))
  have hπ₁surj : Function.Surjective π₁ :=
    φ.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥L)))
  have hker1 : π₁.ker = Subgroup.center ↥L := by
    have hpsi : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))).ker =
        Subgroup.center ↥L := by
      rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center ↥L))
        e.toMonoidHom e.injective, QuotientGroup.ker_mk' (Subgroup.center ↥L)]
    rw [show π₁ = φ.toMonoidHom.comp
          (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))) from rfl,
      MonoidHom.ker_comp_of_injective _ φ.toMonoidHom φ.injective, hpsi]
  have hcardImg : Nat.card ((T.subgroupOf L).map π₁) = 128 := by
    have htop : Nat.card ↥(⊤ : Subgroup ↥(T.subgroupOf L)) =
        Nat.card ↥(T.subgroupOf L) := Subgroup.card_top
    have hinj : Function.Injective (π₁.comp (T.subgroupOf L).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hxZ : (x : ↥L) ∈ Subgroup.center ↥L := by
        rw [← hker1, MonoidHom.mem_ker]; exact hx
      have hxinf : (x : ↥L) ∈ Subgroup.center ↥L ⊓ (T.subgroupOf L) := ⟨hxZ, x.2⟩
      rw [hdisj] at hxinf
      exact Subtype.ext (Subgroup.mem_bot.mp hxinf)
    have hrange : (π₁.comp (T.subgroupOf L).subtype).range = (T.subgroupOf L).map π₁ := by
      ext y; constructor
      · rintro ⟨x, rfl⟩; exact Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
    have h := Subgroup.card_map_of_injective (f := π₁.comp (T.subgroupOf L).subtype) hinj (K := ⊤)
    rw [Subgroup.map_top, hrange, htop, hcardT] at h
    exact h
  have hPT : IsPGroup 2 ((T.subgroupOf L).map π₁) := by
    apply IsPGroup.of_card (n := 7); rw [hcardImg]; norm_num
  have hidxP : ((T.subgroupOf L).map π₁).index = 3465 := by
    have h := Subgroup.card_mul_index ((T.subgroupOf L).map π₁)
    rw [hcardImg, hMgrp] at h; omega
  let P : Sylow 2 ↥Mgrp :=
    IsPGroup.toSylow (P := (T.subgroupOf L).map π₁) hPT (by rw [hidxP]; norm_num)
  have hPU : IsPGroup 2 Ugrp := by
    apply IsPGroup.of_card (n := 7); rw [card_Ugrp]; norm_num
  have hidxU : Ugrp.index = 3465 := by
    have h := Subgroup.card_mul_index Ugrp
    rw [card_Ugrp, hMgrp] at h; omega
  let Q : Sylow 2 ↥Mgrp := IsPGroup.toSylow (P := Ugrp) hPU (by rw [hidxU]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_map_eq_of_sylow P Q
  let π₂ : ↥L →* ↥Mgrp := (MulAut.conj g).toMonoidHom.comp π₁
  have hπ₂surj : Function.Surjective π₂ := (MulAut.conj g).surjective.comp hπ₁surj
  have hker2 : π₂.ker = Subgroup.center ↥L := by
    rw [show π₂ = (MulAut.conj g).toMonoidHom.comp π₁ from rfl,
      MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective, hker1]
  have hcoeP : (P : Subgroup ↥Mgrp) = (T.subgroupOf L).map π₁ := rfl
  have hcoeQ : (Q : Subgroup ↥Mgrp) = Ugrp := rfl
  have hmap2 : (T.subgroupOf L).map π₂ = Ugrp := by
    have h1 : (T.subgroupOf L).map π₂ =
        ((T.subgroupOf L).map π₁).map (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_map]
    rw [h1, ← hcoeP, ← hcoeQ]
    exact hg.symm
  obtain ⟨A, B, hUA, hUB, hAcard0, hBcard0, hunion0, hAB, huniqA0, huniqB0⟩ := mgrp_overgroups
  have hBA : ¬ B ≤ A := by
    intro h
    have hc := Nat.card_le_card_of_injective (Subgroup.inclusion h)
      (Subgroup.inclusion_injective h)
    rw [hBcard0, hAcard0] at hc; omega
  have hAne : A ≠ ⊤ := by
    intro h
    have : Nat.card A = 443520 := by rw [h, Subgroup.card_top]; exact hMgrp
    rw [hAcard0] at this; norm_num at this
  have hBne : B ≠ ⊤ := by
    intro h
    have : Nat.card B = 443520 := by rw [h, Subgroup.card_top]; exact hMgrp
    rw [hBcard0] at this; norm_num at this
  have hTA : (T.subgroupOf L).map π₂ ≤ A := hmap2.le.trans hUA
  have hTB : (T.subgroupOf L).map π₂ ≤ B := hmap2.le.trans hUB
  have hlat : ∀ W : Subgroup ↥Mgrp, (T.subgroupOf L).map π₂ ≤ W →
      W = ⊤ ∨ W ≤ A ∨ W ≤ B := fun W hW => hunion0 W (hmap2 ▸ hW)
  have hAcard : ∀ W : Subgroup ↥Mgrp, (T.subgroupOf L).map π₂ ≤ W →
      Nat.card W = Nat.card A → W = A :=
    fun W hW hWc => huniqA0 W (hmap2 ▸ hW) (hWc.trans hAcard0)
  have hBcard : ∀ W : Subgroup ↥Mgrp, (T.subgroupOf L).map π₂ ≤ W →
      Nat.card W = Nat.card B → W = B :=
    fun W hW hWc => huniqB0 W (hmap2 ▸ hW) (hWc.trans hBcard0)
  obtain ⟨hT'A, hT'B, hcoA, hcoB, hneAB, hcardA', hcardB', hcoatoms, huniqA, huniqB⟩ :=
    maximal_overgroups_of_central_cover π₂ hπ₂surj (le_of_eq hker2) hperf hTA hTB hAne hBne
      hAB hBA hlat hAcard hBcard
  let N₀ : Subgroup ↥L := A.comap π₂
  let M₀ : Subgroup ↥L := B.comap π₂
  let M : Subgroup Γ := M₀.map L.subtype
  let N : Subgroup Γ := N₀.map L.subtype
  have hcardN₀ : Nat.card N₀ = 5760 := by
    change Nat.card (A.comap π₂) = 5760
    rw [hcardA', hker2, hZcard, hAcard0]
  have hcardM₀ : Nat.card M₀ = 17280 := by
    change Nat.card (B.comap π₂) = 17280
    rw [hcardB', hker2, hZcard, hBcard0]
  have hcardM : Nat.card M = 17280 := by
    change Nat.card (M₀.map L.subtype) = 17280
    rw [Subgroup.card_map_of_injective (K := M₀) (f := L.subtype) L.subtype_injective, hcardM₀]
  have hcardN : Nat.card N = 5760 := by
    change Nat.card (N₀.map L.subtype) = 5760
    rw [Subgroup.card_map_of_injective (K := N₀) (f := L.subtype) L.subtype_injective, hcardN₀]
  have hMsub : M.subgroupOf L = M₀ :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective M₀
  have hNsub : N.subgroupOf L = N₀ :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective N₀
  have hmaxM : IsMaximalIn M L :=
    (isCoatom_subgroupOf_iff (Subgroup.map_subtype_le M₀)).mp (by rw [hMsub]; exact hcoB)
  have hmaxN : IsMaximalIn N L :=
    (isCoatom_subgroupOf_iff (Subgroup.map_subtype_le N₀)).mp (by rw [hNsub]; exact hcoA)
  have hMN : M ≠ N := by
    intro h
    exact hneAB (Subgroup.map_injective L.subtype_injective h).symm
  have hTM : T ≤ M := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hT.le]
    exact Subgroup.map_mono hT'B
  have hTN : T ≤ N := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hT.le]
    exact Subgroup.map_mono hT'A
  have hkerM₀ : π₂.ker ≤ M₀ := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_comap, hx]
    exact B.one_mem
  have hZM : (Subgroup.center ↥L).map L.subtype ≤ M := by
    rw [← hker2]
    exact Subgroup.map_mono hkerM₀
  have hZN : (Subgroup.center ↥L).map L.subtype ≤ N := by
    have hkerN₀ : π₂.ker ≤ N₀ := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      rw [Subgroup.mem_comap, hx]
      exact A.one_mem
    rw [← hker2]
    exact Subgroup.map_mono hkerN₀
  have hclass : ∀ Y : Subgroup Γ, IsMaximalIn Y L → T ≤ Y → Y = M ∨ Y = N := by
    intro Y hmaxY hTY
    have hYle : Y ≤ L := le_of_lt hmaxY.1
    have hco : IsCoatom (Y.subgroupOf L) := (isCoatom_subgroupOf_iff hYle).mpr hmaxY
    have hT'Y : T.subgroupOf L ≤ Y.subgroupOf L := (subgroupOf_le_subgroupOf_iff hT.le hYle).mpr hTY
    rcases hcoatoms (Y.subgroupOf L) hco hT'Y with h | h
    · right; rw [← Subgroup.map_subgroupOf_eq_of_le hYle, h]
    · left; rw [← Subgroup.map_subgroupOf_eq_of_le hYle, h]
  have huniqM : ∀ Y : Subgroup Γ, Y ≤ L → T ≤ Y → (Subgroup.center ↥L).map L.subtype ≤ Y →
      Nat.card Y = 17280 → Y = M := by
    intro Y hYle hTY hZY hYcard
    have hT'Y : T.subgroupOf L ≤ Y.subgroupOf L := (subgroupOf_le_subgroupOf_iff hT.le hYle).mpr hTY
    have hZ'Y : π₂.ker ≤ Y.subgroupOf L := by
      rw [hker2]; exact (Subgroup.map_le_iff_le_comap).mp hZY
    have hY'c : Nat.card (Y.subgroupOf L) = Nat.card π₂.ker * Nat.card B := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYle).toEquiv, hYcard, hker2, hZcard,
        hBcard0]
    have h := huniqB (Y.subgroupOf L) hT'Y hZ'Y hY'c
    rw [← Subgroup.map_subgroupOf_eq_of_le hYle, h]
  have huniqN : ∀ Y : Subgroup Γ, Y ≤ L → T ≤ Y → (Subgroup.center ↥L).map L.subtype ≤ Y →
      Nat.card Y = 5760 → Y = N := by
    intro Y hYle hTY hZY hYcard
    have hT'Y : T.subgroupOf L ≤ Y.subgroupOf L := (subgroupOf_le_subgroupOf_iff hT.le hYle).mpr hTY
    have hZ'Y : π₂.ker ≤ Y.subgroupOf L := by
      rw [hker2]; exact (Subgroup.map_le_iff_le_comap).mp hZY
    have hY'c : Nat.card (Y.subgroupOf L) = Nat.card π₂.ker * Nat.card A := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYle).toEquiv, hYcard, hker2, hZcard,
        hAcard0]
    have h := huniqA (Y.subgroupOf L) hT'Y hZ'Y hY'c
    rw [← Subgroup.map_subgroupOf_eq_of_le hYle, h]
  exact ⟨M, N, Subgroup.map_subtype_le M₀, Subgroup.map_subtype_le N₀, hTM, hTN, hZM, hZN,
    hcardM, hcardN, hmaxM, hmaxN, hMN, hclass, huniqM, huniqN⟩

end CFSG.Quasithin.AppendixH.H12
