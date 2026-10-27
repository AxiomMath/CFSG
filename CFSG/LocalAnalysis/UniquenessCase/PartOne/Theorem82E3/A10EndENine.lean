module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndKeySetup
import CFSG.GroupTheory.CardMapInfKer
import CFSG.GroupTheory.PGroup.CardCoprime
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace A10Perm

open Equiv Equiv.Perm Subgroup
open CFSG.GH74.Uniqueness.SU.SU13.TA.L10

@[expose] def sigma : Perm (Fin 10) := toP 2 2 2

@[expose] def tau : Perm (Fin 10) := pw

@[expose] def eNine : Subgroup (Perm (Fin 10)) := Subgroup.closure {sigma, tau}

private def carrierNine : Set (Perm (Fin 10)) :=
  {x | ∃ i j : Fin 3, x = sigma ^ (i : ℕ) * tau ^ (j : ℕ)}

private def eNineF : Subgroup (Perm (Fin 10)) where
  carrier := carrierNine
  one_mem' := ⟨0, 0, by decide +kernel⟩
  mul_mem' := by
    intro x y hx hy
    obtain ⟨i, j, hx'⟩ := hx
    obtain ⟨k, l, hy'⟩ := hy
    refine ⟨i + k, j + l, ?_⟩
    rw [hx', hy']
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide +kernel
  inv_mem' := by
    intro x hx
    obtain ⟨i, j, hx'⟩ := hx
    refine ⟨i + i, j + j, ?_⟩
    rw [hx']
    fin_cases i <;> fin_cases j <;> decide +kernel

private theorem eNine_eq_eNineF : eNine = eNineF := by
  apply le_antisymm
  · rw [eNine, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by decide +kernel⟩
    · exact ⟨0, 1, by decide +kernel⟩
  · intro x hx
    obtain ⟨i, j, rfl⟩ := hx
    exact Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem mem_eNine_iff {x : Perm (Fin 10)} :
    x ∈ eNine ↔ ∃ i j : Fin 3, x = sigma ^ (i : ℕ) * tau ^ (j : ℕ) := by
  rw [eNine_eq_eNineF]
  rfl

theorem support_card_of_mem_eNine {x : Perm (Fin 10)} (hx : x ∈ eNine) (h1 : x ≠ 1) :
    x.support.card = 9 := by
  obtain ⟨i, j, hx⟩ := mem_eNine_iff.mp hx
  subst hx
  fin_cases i <;> fin_cases j <;>
    first
      | (exfalso; exact h1 (by decide +kernel))
      | decide +kernel

theorem card_eNine : Nat.card eNine = 9 := by
  rw [eNine_eq_eNineF]
  let f : Fin 3 × Fin 3 → eNineF := fun p =>
    ⟨sigma ^ (p.1 : ℕ) * tau ^ (p.2 : ℕ), ⟨p.1, p.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, j⟩ ⟨k, l⟩ h
      have h' := congrArg (fun x : eNineF => (x : Perm (Fin 10))) h
      simp only [f] at h'
      have hinj : ∀ (i j k l : Fin 3),
          sigma ^ (i : ℕ) * tau ^ (j : ℕ) = sigma ^ (k : ℕ) * tau ^ (l : ℕ) →
            i = k ∧ j = l := by
        intro i j k l h
        revert h
        fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide +kernel
      obtain ⟨rfl, rfl⟩ := hinj i j k l h'
      rfl
    · rintro ⟨x, hx⟩
      obtain ⟨i, j, hx⟩ := hx
      subst hx
      exact ⟨(i, j), rfl⟩
  rw [← Nat.card_eq_of_bijective f hf]
  simp [Nat.card_prod]

theorem isElemAbelian_eNine : CFSG.Open.IsElemAbelian 3 eNine := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨i, j, hx⟩ := mem_eNine_iff.mp x.2
    obtain ⟨k, l, hy⟩ := mem_eNine_iff.mp y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hx, hy]
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide +kernel
  · obtain ⟨i, j, rfl⟩ := mem_eNine_iff.mp hx
    fin_cases i <;> fin_cases j <;> decide +kernel

theorem eNine_le_alternatingGroup : eNine ≤ alternatingGroup (Fin 10) := by
  rw [eNine, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact Perm.mem_alternatingGroup.mpr (by decide +kernel)
  · exact Perm.mem_alternatingGroup.mpr sign_pw

theorem cycleType_eq_replicate_three {x : Perm (Fin 10)} (h3 : x ^ 3 = 1) (h1 : x ≠ 1)
    (hs : x.support.card = 9) : x.cycleType = Multiset.replicate 3 3 := by
  have hord : orderOf x = 3 := orderOf_eq_prime h3 h1
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (hord ▸ Nat.prime_three)
  rw [hord] at hn
  have hsum := congrArg Multiset.sum hn
  rw [Equiv.Perm.sum_cycleType, Multiset.sum_replicate, smul_eq_mul, hs] at hsum
  have hn3 : n + 1 = 3 := by omega
  rw [hn, hn3]

theorem cycleType_sigma : sigma.cycleType = Multiset.replicate 3 3 :=
  cycleType_eq_replicate_three (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def oddSig : Perm (Fin 10) := swap 0 3 * swap 1 4 * swap 2 5

private theorem sign_oddSig : Equiv.Perm.sign oddSig = -1 := by decide +kernel

private theorem oddSig_mul_sigma : oddSig * sigma * oddSig⁻¹ = sigma := by decide +kernel

private theorem exists_even_conj_sigma {x : Perm (Fin 10)} (hx : x ∈ alternatingGroup (Fin 10))
    (hc : x.cycleType = Multiset.replicate 3 3) :
    ∃ g ∈ alternatingGroup (Fin 10), g * x * g⁻¹ = sigma := by
  obtain ⟨g, hg⟩ := isConj_iff.mp
    ((Equiv.Perm.isConj_iff_cycleType_eq).mpr (hc.trans cycleType_sigma.symm))
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hsign | hsign
  · exact ⟨g, Perm.mem_alternatingGroup.mpr hsign, hg⟩
  · refine ⟨oddSig * g, ?_, ?_⟩
    · rw [Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, sign_oddSig, hsign]
      norm_num
    · calc (oddSig * g) * x * (oddSig * g)⁻¹ = oddSig * (g * x * g⁻¹) * oddSig⁻¹ := by group
        _ = oddSig * sigma * oddSig⁻¹ := by rw [hg]
        _ = sigma := oddSig_mul_sigma

theorem exists_mem_alternatingGroup_conj {x y : Perm (Fin 10)}
    (hx : x ∈ alternatingGroup (Fin 10)) (hy : y ∈ alternatingGroup (Fin 10))
    (hcx : x.cycleType = Multiset.replicate 3 3) (hcy : y.cycleType = Multiset.replicate 3 3) :
    ∃ g ∈ alternatingGroup (Fin 10), g * x * g⁻¹ = y := by
  obtain ⟨g₁, hg₁A, hg₁⟩ := exists_even_conj_sigma hx hcx
  obtain ⟨g₂, hg₂A, hg₂⟩ := exists_even_conj_sigma hy hcy
  refine ⟨g₂⁻¹ * g₁, Subgroup.mul_mem _ (Subgroup.inv_mem _ hg₂A) hg₁A, ?_⟩
  calc (g₂⁻¹ * g₁) * x * (g₂⁻¹ * g₁)⁻¹ = g₂⁻¹ * (g₁ * x * g₁⁻¹) * g₂ := by group
    _ = g₂⁻¹ * sigma * g₂ := by rw [hg₁]
    _ = y := by
        rw [← hg₂]
        group

end A10Perm

namespace Ctx82E3.A10Frame

variable {c : Ctx82E3 D} (F : A10Frame c)

@[expose] noncomputable def phiL : ↥c.L →* Equiv.Perm (Fin 10) :=
  F.phiA.comp (Subgroup.inclusion c.hyp81.1)

theorem phiL_apply (x : ↥c.L) : F.phiL x = F.phiA ⟨x, c.hyp81.1 x.2⟩ := rfl

theorem phiL_range : F.phiL.range = alternatingGroup (Fin 10) := by
  rw [phiL, MonoidHom.range_comp, Subgroup.inclusion_range, F.map_L_phiA]

theorem phiL_ker : F.phiL.ker = CFSG.Open.pCore 2 ↥c.L := by
  ext x
  rw [MonoidHom.mem_ker, phiL_apply, F.phiA_eq_one_iff x.2]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem isPGroup_ker_phiL : IsPGroup 2 ↥F.phiL.ker := by
  rw [phiL_ker]
  exact CFSG.pCore_isPGroup

theorem eNine_le_range_phiL : A10Perm.eNine ≤ F.phiL.range := by
  rw [phiL_range]
  exact A10Perm.eNine_le_alternatingGroup

@[expose] noncomputable def Ynine : Subgroup ↥c.L :=
  A10Perm.eNine.comap F.phiL

theorem Ynine_map : F.Ynine.map F.phiL = A10Perm.eNine :=
  Subgroup.map_comap_eq_self F.eNine_le_range_phiL

theorem deg_zpowers_of_mem_Ynine {x : ↥c.L} (hx : x ∈ F.Ynine)
    (hx1 : F.phiL x ≠ 1) : F.deg (Subgroup.zpowers (x : G)) = 9 := by
  have hsupp : (F.phiL x).support.card = 9 :=
    A10Perm.support_card_of_mem_eNine hx hx1
  rw [F.deg_zpowers_eq x.2, ← F.phiL_apply]
  exact hsupp

private theorem isElemAbelian_of_map_eNine (F : A10Frame c) {S : Subgroup ↥c.L}
    (hS3 : IsPGroup 3 S) (hSmap : S.map F.phiL = A10Perm.eNine) :
    CFSG.Open.IsElemAbelian 3 S := by
  have hSker : S ⊓ F.phiL.ker = ⊥ :=
    (IsPGroup.disjoint_of_coprime hS3 F.isPGroup_ker_phiL
      (by norm_num : Nat.Coprime 3 2)).eq_bot
  have hcomm : ∀ x ∈ S, ∀ y ∈ S,
      F.phiL x * F.phiL y = F.phiL y * F.phiL x := by
    intro x hx y hy
    have hx' : F.phiL x ∈ A10Perm.eNine := by
      rw [← hSmap]; exact Subgroup.mem_map_of_mem F.phiL hx
    have hy' : F.phiL y ∈ A10Perm.eNine := by
      rw [← hSmap]; exact Subgroup.mem_map_of_mem F.phiL hy
    have h := A10Perm.isElemAbelian_eNine.1.is_comm.comm
      (⟨F.phiL x, hx'⟩ : ↥A10Perm.eNine) ⟨F.phiL y, hy'⟩
    simpa using congrArg Subtype.val h
  have hinj : ∀ a ∈ S, ∀ b ∈ S, F.phiL a = F.phiL b → a = b := by
    intro a ha b hb hab
    have hmem : a⁻¹ * b ∈ S ⊓ F.phiL.ker :=
      ⟨S.mul_mem (S.inv_mem ha) hb, by
        show F.phiL (a⁻¹ * b) = 1
        rw [map_mul, map_inv, hab, inv_mul_cancel]⟩
    rw [hSker] at hmem
    exact inv_mul_eq_one.mp (Subgroup.mem_bot.mp hmem)
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    exact hinj ((a : ↥c.L) * (b : ↥c.L)) (S.mul_mem a.2 b.2) ((b : ↥c.L) * (a : ↥c.L))
      (S.mul_mem b.2 a.2) (by rw [map_mul, map_mul]; exact hcomm (a : ↥c.L) a.2 (b : ↥c.L) b.2)
  · have hx' : F.phiL x ∈ A10Perm.eNine := by
      rw [← hSmap]; exact Subgroup.mem_map_of_mem F.phiL hx
    have hmem : x ^ 3 ∈ S ⊓ F.phiL.ker := by
      refine ⟨S.pow_mem hx 3, ?_⟩
      show F.phiL (x ^ 3) = 1
      rw [map_pow]
      exact A10Perm.isElemAbelian_eNine.2 (F.phiL x) hx'
    rw [hSker] at hmem
    exact Subgroup.mem_bot.mp hmem

private theorem exists_sylow_le_Ynine_map :
    ∃ E : Subgroup ↥c.L, E ≤ F.Ynine ∧ IsPGroup 3 E ∧ Nat.card E = 9 ∧
      E.map F.phiL = A10Perm.eNine := by
  classical
  let P : Subgroup ↥c.L := F.Ynine
  have hPmap : P.map F.phiL = A10Perm.eNine := F.Ynine_map
  let φ : ↥P →* ↥A10Perm.eNine :=
    (F.phiL.domRestrict P).codRestrict A10Perm.eNine
      (fun x => hPmap ▸ Subgroup.mem_map_of_mem F.phiL x.2)
  have hφsurj : Function.Surjective φ := by
    intro t
    have ht : (t : Equiv.Perm (Fin 10)) ∈ P.map F.phiL := by
      rw [hPmap]
      exact t.2
    obtain ⟨p, hp, hpt⟩ := Subgroup.mem_map.mp ht
    exact ⟨⟨p, hp⟩, Subtype.ext hpt⟩
  have hSe : IsPGroup 3 (⊤ : Subgroup ↥A10Perm.eNine) :=
    (CFSG.Open.IsElemAbelian.isPGroup A10Perm.isElemAbelian_eNine).of_equiv
      Subgroup.topEquiv.symm
  let S : Sylow 3 ↥P := Sylow.nonempty.some
  have htop : (S : Subgroup ↥P).map φ = ⊤ := by
    have h := (S.mapSurjective hφsurj).is_maximal' (Q := ⊤) hSe le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  have hSker : (S : Subgroup ↥P) ⊓ φ.ker = ⊥ := by
    have h2 : IsPGroup 2 ↥(φ.ker) := by
      have hker : φ.ker = F.phiL.ker.subgroupOf P := by
        ext x
        simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, φ, MonoidHom.codRestrict_apply,
          MonoidHom.domRestrict_apply, Subtype.ext_iff, OneMemClass.coe_one]
      rw [hker]
      exact F.isPGroup_ker_phiL.comap_subtype
    exact (IsPGroup.disjoint_of_coprime S.isPGroup' h2
      (by norm_num : Nat.Coprime 3 2)).eq_bot
  have hcardS : Nat.card ↥(S : Subgroup ↥P) = 9 := by
    have h1 : Nat.card ↥((S : Subgroup ↥P).map φ) = Nat.card ↥(S : Subgroup ↥P) :=
      CFSG.card_map_eq_card_of_inf_ker_eq_bot φ hSker
    rw [htop] at h1
    rw [← h1, Nat.card_congr Subgroup.topEquiv.toEquiv, A10Perm.card_eNine]
  have hcomp : F.phiL.comp P.subtype = A10Perm.eNine.subtype.comp φ :=
    MonoidHom.ext fun x => rfl
  have hSmap : ((S : Subgroup ↥P).map P.subtype).map F.phiL = A10Perm.eNine := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, htop, Subgroup.map_top,
      Subgroup.range_subtype]
  exact ⟨(S : Subgroup ↥P).map P.subtype, Subgroup.map_subtype_le (S : Subgroup ↥P),
    S.isPGroup'.map P.subtype,
    (Subgroup.card_map_of_injective (K := (S : Subgroup ↥P))
      P.subtype_injective).trans hcardS, hSmap⟩

theorem deg_zpowers_eq_phiL (x : ↥c.L) :
    F.deg (Subgroup.zpowers (x : G)) = (F.phiL x).support.card := by
  rw [F.deg_zpowers_eq x.2, ← F.phiL_apply]

private theorem isSylowOf_zpowers_of_mem_comap (F : A10Frame c) {g : Equiv.Perm (Fin 10)}
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (hgrange : g ∈ F.phiL.range) {z : ↥c.L}
    (hzZ : z ∈ (Subgroup.zpowers g).comap F.phiL) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    CFSG.ABGLocalTools.IsSylowOf 3 (Subgroup.zpowers z)
      ((Subgroup.zpowers g).comap F.phiL) := by
  classical
  let Z : Subgroup ↥c.L := (Subgroup.zpowers g).comap F.phiL
  have hker_le : F.phiL.ker ≤ Z := by
    intro k hk
    exact Subgroup.mem_comap.mpr (by rw [MonoidHom.mem_ker.mp hk]; exact Subgroup.one_mem _)
  have hZmap : Z.map F.phiL = Subgroup.zpowers g :=
    Subgroup.map_comap_eq_self (Subgroup.zpowers_le.mpr hgrange)
  have hZcard : Nat.card ↥Z = 3 * Nat.card ↥F.phiL.ker := by
    have h1 := Subgroup.card_ker_mul_card_range (F.phiL.domRestrict Z)
    have hrange : (F.phiL.domRestrict Z).range = Subgroup.zpowers g := by
      rw [show F.phiL.domRestrict Z = F.phiL.comp Z.subtype from rfl, MonoidHom.range_comp,
        Subgroup.range_subtype, hZmap]
    have hkereq : (F.phiL.domRestrict Z).ker = F.phiL.ker.subgroupOf Z :=
      MonoidHom.ker_domRestrict Z F.phiL
    have hkercard : Nat.card ↥((F.phiL.domRestrict Z).ker) = Nat.card ↥F.phiL.ker := by
      rw [hkereq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv
    have hrangcard : Nat.card ↥((F.phiL.domRestrict Z).range) = 3 := by
      rw [hrange, Nat.card_zpowers, orderOf_eq_prime hg3 hg1]
    rw [hkercard, hrangcard] at h1
    omega
  have hcard : Nat.card ↥(Subgroup.zpowers z) = 3 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime hz3 hz1
  have hrel : (Subgroup.zpowers z).relIndex Z * 3 = 3 * Nat.card ↥F.phiL.ker := by
    have h := Subgroup.relIndex_mul_card (H := Subgroup.zpowers z) (K := Z)
    rw [inf_eq_left.mpr (Subgroup.zpowers_le.mpr hzZ), hcard] at h
    rw [h, hZcard]
  have hnotdvd : ¬ 3 ∣ (Subgroup.zpowers z).relIndex Z := by
    obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq (p := 2) F.isPGroup_ker_phiL
    have hrel2 : (Subgroup.zpowers z).relIndex Z = Nat.card ↥F.phiL.ker := by omega
    rw [hrel2, hn]
    intro h
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at h32
  exact CFSG.ABGLocalTools.isSylowOf_iff.mpr
    ⟨Subgroup.zpowers_le.mpr hzZ,
      IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num), hnotdvd⟩

private theorem support_phiL_of_deg_nine (F : A10Frame c) {x : ↥c.L}
    (hxd : F.deg (Subgroup.zpowers (x : G)) = 9) : (F.phiL x).support.card = 9 := by
  rw [← F.deg_zpowers_eq_phiL]; exact hxd

private theorem ne_one_of_support_card_nine {x : Equiv.Perm (Fin 10)}
    (hx : x.support.card = 9) : x ≠ 1 := by
  intro h
  rw [h, Equiv.Perm.support_one, Finset.card_empty] at hx
  exact absurd hx (by norm_num)

private theorem cycleType_phiL_of_deg_nine (F : A10Frame c) {x : ↥c.L} (hx3 : x ^ 3 = 1)
    (hxd : F.deg (Subgroup.zpowers (x : G)) = 9) :
    (F.phiL x).cycleType = Multiset.replicate 3 3 := by
  have hsupp := F.support_phiL_of_deg_nine hxd
  exact A10Perm.cycleType_eq_replicate_three (by rw [← map_pow, hx3, map_one])
    (ne_one_of_support_card_nine hsupp) hsupp

private theorem exists_conj_zpowers_of_deg_nine {x y : ↥c.L}
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxd : F.deg (Subgroup.zpowers (x : G)) = 9)
    (hyd : F.deg (Subgroup.zpowers (y : G)) = 9) :
    ∃ l : ↥c.L, l * x * l⁻¹ ∈ Subgroup.zpowers y := by
  classical
  have hy3' : (F.phiL y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hy1' : F.phiL y ≠ 1 :=
    ne_one_of_support_card_nine (F.support_phiL_of_deg_nine hyd)
  have hxcyc : (F.phiL x).cycleType = Multiset.replicate 3 3 :=
    F.cycleType_phiL_of_deg_nine hx3 hxd
  have hycyc : (F.phiL y).cycleType = Multiset.replicate 3 3 :=
    F.cycleType_phiL_of_deg_nine hy3 hyd
  have hxA : F.phiL x ∈ alternatingGroup (Fin 10) :=
    F.phiL_range ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩
  have hyA : F.phiL y ∈ alternatingGroup (Fin 10) :=
    F.phiL_range ▸ MonoidHom.mem_range.mpr ⟨y, rfl⟩
  obtain ⟨g, hgA, hg⟩ := A10Perm.exists_mem_alternatingGroup_conj hxA hyA hxcyc hycyc
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (by rw [F.phiL_range]; exact hgA)
  let x' : ↥c.L := m * x * m⁻¹
  have hx'map : F.phiL x' = F.phiL y := by
    calc F.phiL x' = F.phiL m * F.phiL x * (F.phiL m)⁻¹ := by
          rw [show x' = m * x * m⁻¹ from rfl, map_mul, map_mul, map_inv]
      _ = g * F.phiL x * g⁻¹ := by rw [hm]
      _ = F.phiL y := hg
  have hyZ : y ∈ (Subgroup.zpowers (F.phiL y)).comap F.phiL :=
    Subgroup.mem_comap.mpr (Subgroup.mem_zpowers _)
  have hx'Z : x' ∈ (Subgroup.zpowers (F.phiL y)).comap F.phiL :=
    Subgroup.mem_comap.mpr (hx'map ▸ Subgroup.mem_zpowers _)
  have hx'3 : x' ^ 3 = 1 := by
    rw [show x' = MulAut.conj m x by rw [MulAut.conj_apply], ← map_pow, hx3, map_one]
  have hx'1 : x' ≠ 1 := fun h => hy1' (by rw [← hx'map, h]; exact map_one F.phiL)
  have hyrange : F.phiL y ∈ F.phiL.range := MonoidHom.mem_range.mpr ⟨y, rfl⟩
  obtain ⟨k, hkZ, hkconj⟩ :=
    (F.isSylowOf_zpowers_of_mem_comap hy3' hy1' hyrange hyZ hy3 hy1).exists_mem_conj
      (F.isSylowOf_zpowers_of_mem_comap hy3' hy1' hyrange hx'Z hx'3 hx'1)
  refine ⟨k⁻¹ * m, ?_⟩
  · have hmem : k⁻¹ * x' * k ∈ Subgroup.zpowers y :=
      (hkconj x').mp (Subgroup.mem_zpowers x')
    have heq : (k⁻¹ * m) * x * (k⁻¹ * m)⁻¹ = k⁻¹ * x' * k := by
      rw [show x' = m * x * m⁻¹ from rfl]
      group
    rw [heq]
    exact hmem

private theorem exists_mem_centralizer_ne_bot (F : A10Frame c) {U : Subgroup G}
    (hU : IsPGroup 2 U) (hU1 : U ≠ ⊥) (hLU : c.L ≤ Subgroup.normalizer (U : Set G))
    {E : Subgroup ↥c.L} (hEea : CFSG.Open.IsElemAbelian 3 E) (hEcard : Nat.card E = 9) :
    ∃ e ∈ E, (e : G) ≠ 1 ∧ U ⊓ Subgroup.centralizer ({(e : G)} : Set G) ≠ ⊥ := by
  classical
  let E' : Subgroup G := E.map c.L.subtype
  have hE'ea : CFSG.Open.IsElemAbelian 3 E' := hEea.map c.L.subtype
  have hE'card : Nat.card E' = 9 :=
    (Subgroup.card_map_of_injective (K := E) c.L.subtype_injective).trans hEcard
  have hE'N : E' ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.map_subtype_le E).trans hLU
  have hcop : ¬ 3 ∣ Nat.card U :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (G := ↥U) hU Nat.prime_three (by norm_num)
  have hgen := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma123.le_iSup_inf_centralizer
    (p := 3) (P := E') (X := U) hE'ea (by rw [hE'card]; norm_num) hcop hE'N
  have hex : ∃ e ∈ E', e ≠ 1 ∧ U ⊓ Subgroup.centralizer ({e} : Set G) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have hsup : (⨆ (e : G) (_ : e ∈ E') (_ : e ≠ 1),
        U ⊓ Subgroup.centralizer ({e} : Set G)) = ⊥ := by
      rw [iSup_eq_bot]
      intro e
      rw [iSup_eq_bot]
      intro he
      rw [iSup_eq_bot]
      intro he1
      exact hcon e he he1
    rw [hsup] at hgen
    exact hU1 (le_bot_iff.mp hgen)
  obtain ⟨e', he', he'1, hue'⟩ := hex
  obtain ⟨e, heE, rfl⟩ := Subgroup.mem_map.mp he'
  exact ⟨e, heE, he'1, hue'⟩

private theorem exists_zpowers_eq_of_card_three {B : Subgroup G} (hB3 : Nat.card B = 3) :
    ∃ b : G, B = Subgroup.zpowers b ∧ b ^ 3 = 1 ∧ b ≠ 1 := by
  classical
  have hBne : B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hB3
    exact absurd hB3 (by norm_num)
  obtain ⟨bB, hbB1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hb1 : (bB : G) ≠ 1 := fun h => hbB1 (Subtype.ext h)
  have hb3 : (bB : G) ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥B) (x := bB)
    rw [hB3] at h
    have := congrArg Subtype.val h
    simpa using this
  refine ⟨(bB : G), ?_, hb3, hb1⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr bB.2)
  rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
  exact hB3.le

private theorem exists_zpowers_conj_eq (F : A10Frame c) {b : G} (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (hbL : b ∈ c.L) {e₀ : ↥c.L} (he₀3 : e₀ ^ 3 = 1) (he₀1 : e₀ ≠ 1)
    (he₀d : F.deg (Subgroup.zpowers (e₀ : G)) = 9) (hbd : F.deg (Subgroup.zpowers b) = 9) :
    ∃ l : ↥c.L, Subgroup.zpowers ((l : G) * (e₀ : G) * (l : G)⁻¹) = Subgroup.zpowers b := by
  classical
  let bL : ↥c.L := ⟨b, hbL⟩
  have hb3L : bL ^ 3 = 1 := by
    apply Subtype.ext
    show b ^ 3 = 1
    exact hb3
  have hb1L : bL ≠ 1 := by
    intro h
    exact hb1 (congrArg Subtype.val h)
  have hbdL : F.deg (Subgroup.zpowers (bL : G)) = 9 := hbd
  obtain ⟨l, hl⟩ := F.exists_conj_zpowers_of_deg_nine he₀3 hb3L he₀1 hb1L he₀d hbdL
  refine ⟨l, ?_⟩
  have hle : (l : G) * (e₀ : G) * (l : G)⁻¹ ∈ Subgroup.zpowers b := by
    have h := Subgroup.mem_map_of_mem c.L.subtype hl
    rwa [MonoidHom.map_zpowers] at h
  have he₀3G : (e₀ : G) ^ 3 = 1 := by
    simpa using congrArg (fun z : ↥c.L => (z : G)) he₀3
  have hconj3 : ((l : G) * (e₀ : G) * (l : G)⁻¹) ^ 3 = 1 := by
    have h1 : (l : G) * (e₀ : G) * (l : G)⁻¹ = MulAut.conj (l : G) (e₀ : G) := by
      rw [MulAut.conj_apply]
    rw [h1, ← map_pow, he₀3G, map_one]
  have hconj1 : (l : G) * (e₀ : G) * (l : G)⁻¹ ≠ 1 := by
    intro h
    apply he₀1
    have h2 : (l : G)⁻¹ * ((l : G) * (e₀ : G) * (l : G)⁻¹) * (l : G) = (e₀ : G) := by
      group
    rw [h] at h2
    simp at h2
    exact Subtype.ext h2.symm
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hle)
  rw [Nat.card_zpowers b, Nat.card_zpowers ((l : G) * (e₀ : G) * (l : G)⁻¹),
    orderOf_eq_prime hb3 hb1, orderOf_eq_prime hconj3 hconj1]

private theorem inf_centralizer_ne_bot_of_commutes (F : A10Frame c) {U : Subgroup G}
    (hLU : c.L ≤ Subgroup.normalizer (U : Set G))
    {B : Subgroup G} {b : G} (hBz : B = Subgroup.zpowers b) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (hbL : b ∈ c.L) (hbd : F.deg (Subgroup.zpowers b) = 9)
    {e₀ : ↥c.L} (he₀3 : e₀ ^ 3 = 1) (he₀1 : e₀ ≠ 1)
    (he₀d : F.deg (Subgroup.zpowers (e₀ : G)) = 9)
    {u : G} (huU : u ∈ U) (hu1 : u ≠ 1) (hucomm : u * (e₀ : G) = (e₀ : G) * u) :
    U ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ := by
  classical
  have hbB : b ∈ B := by rw [hBz]; exact Subgroup.mem_zpowers b
  obtain ⟨l, hz⟩ := F.exists_zpowers_conj_eq hb3 hb1 hbL he₀3 he₀1 he₀d hbd
  let v : G := (l : G) * u * (l : G)⁻¹
  have hvU : v ∈ U := by
    have hlN : (l : G) ∈ Subgroup.normalizer (U : Set G) := hLU l.2
    exact (Subgroup.mem_normalizer_iff.mp hlN u).mp huU
  have hv1 : v ≠ 1 := by
    intro h
    apply hu1
    have h2 : (l : G)⁻¹ * v * (l : G) = u := by
      simp only [v]
      group
    rw [h, mul_one, inv_mul_cancel] at h2
    exact h2.symm
  have hvC : v ∈ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hcomm : Commute v ((l : G) * (e₀ : G) * (l : G)⁻¹) := by
      show ((l : G) * u * (l : G)⁻¹) * ((l : G) * (e₀ : G) * (l : G)⁻¹) =
        ((l : G) * (e₀ : G) * (l : G)⁻¹) * ((l : G) * u * (l : G)⁻¹)
      calc ((l : G) * u * (l : G)⁻¹) * ((l : G) * (e₀ : G) * (l : G)⁻¹)
          = (l : G) * (u * (e₀ : G)) * (l : G)⁻¹ := by group
        _ = (l : G) * ((e₀ : G) * u) * (l : G)⁻¹ := by rw [hucomm]
        _ = ((l : G) * (e₀ : G) * (l : G)⁻¹) * ((l : G) * u * (l : G)⁻¹) := by group
    have hwB : w ∈ Subgroup.zpowers b := hBz ▸ hw
    have hwz : w ∈ Subgroup.zpowers ((l : G) * (e₀ : G) * (l : G)⁻¹) := by
      rw [hz]
      exact hwB
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hwz
    rw [← hn]
    exact (hcomm.zpow_right n).eq.symm
  intro hbot
  have hmem : v ∈ U ⊓ Subgroup.centralizer (B : Set G) := ⟨hvU, hvC⟩
  rw [hbot] at hmem
  exact hv1 (Subgroup.mem_bot.mp hmem)

theorem inf_centralizer_ne_bot_of_deg_nine (F : A10Frame c) {U : Subgroup G}
    (hU : IsPGroup 2 U) (hU1 : U ≠ ⊥) (hLU : c.L ≤ Subgroup.normalizer (U : Set G))
    {B : Subgroup G} (hBA : B ≤ F.A) (hB3 : Nat.card B = 3) (hB9 : F.deg B = 9) :
    U ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ := by
  classical
  obtain ⟨b, hBz, hb3, hb1⟩ := exists_zpowers_eq_of_card_three hB3
  have hbB : b ∈ B := by rw [hBz]; exact Subgroup.mem_zpowers b
  have hbL : b ∈ c.L := F.P_le_L (F.A_le (hBA hbB))
  have hbd : F.deg (Subgroup.zpowers b) = 9 := by rw [← hBz]; exact hB9
  obtain ⟨E, hEY, hE3, hEcard, hEmap⟩ := F.exists_sylow_le_Ynine_map
  have hEea : CFSG.Open.IsElemAbelian 3 E := F.isElemAbelian_of_map_eNine hE3 hEmap
  obtain ⟨e₀, he₀E, he₀1G, hue⟩ :=
    F.exists_mem_centralizer_ne_bot hU hU1 hLU hEea hEcard
  have he₀1 : e₀ ≠ 1 := fun h => he₀1G (by rw [h]; rfl)
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hue
  have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have huU : (u : G) ∈ U := u.2.1
  have huC : (u : G) ∈ Subgroup.centralizer ({(e₀ : G)} : Set G) := u.2.2
  have hucomm : (u : G) * (e₀ : G) = (e₀ : G) * (u : G) :=
    (Subgroup.mem_centralizer_iff.mp huC (e₀ : G) (by simp)).symm
  have hEker : E ⊓ F.phiL.ker = ⊥ := by
    have h3 : IsPGroup 3 ↥E := CFSG.Open.IsElemAbelian.isPGroup hEea
    have h2 : IsPGroup 2 ↥F.phiL.ker := F.isPGroup_ker_phiL
    exact (IsPGroup.disjoint_of_coprime h3 h2 (by norm_num)).eq_bot
  have he₀3 : e₀ ^ 3 = 1 := hEea.2 e₀ he₀E
  have he₀d : F.deg (Subgroup.zpowers (e₀ : G)) = 9 := by
    have hx1 : F.phiL e₀ ≠ 1 := by
      intro h
      have hmem : e₀ ∈ E ⊓ F.phiL.ker := ⟨he₀E, by
        show F.phiL e₀ = 1
        exact h⟩
      rw [hEker] at hmem
      exact he₀1 (Subgroup.mem_bot.mp hmem)
    exact F.deg_zpowers_of_mem_Ynine (hEY he₀E) hx1
  exact F.inf_centralizer_ne_bot_of_commutes hLU hBz hb3 hb1 hbL hbd he₀3 he₀1 he₀d
    huU hu1' hucomm

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
