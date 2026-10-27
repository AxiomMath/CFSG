module

public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry
import CFSG.LocalAnalysis.RankThreeUC.StronglyEmbedded

public section

namespace CFSG.RankThree.PartOne

open Subgroup
open CFSG.ABGLocalTools
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

private theorem exists_isSylowOf_ge' {p : ℕ} [Fact p.Prime] {R H : Subgroup G}
    (hR : IsPGroup p R) (hRH : R ≤ H) :
    ∃ T : Subgroup G, R ≤ T ∧ CFSG.ABGLocalTools.IsSylowOf p T H := by
  obtain ⟨Q, hQ⟩ := (hR.comap_subtype (K := H)).exists_le_sylow
  exact ⟨(Q : Subgroup H).map H.subtype, fun x hx => ⟨⟨x, hRH hx⟩, hQ hx, rfl⟩, Q, rfl⟩

private theorem exists_mem_center_orderOf_eq' {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hPp : IsPGroup p P) (hP1 : P ≠ ⊥) :
    ∃ u : P, u ∈ Subgroup.center P ∧ orderOf u = p := by
  have hnt : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP1
  have hZnt : Nontrivial (Subgroup.center P) := hPp.center_nontrivial
  have hdvd : p ∣ Nat.card (Subgroup.center P) := by
    obtain ⟨k, hk⟩ := (hPp.to_subgroup (Subgroup.center P)).exists_card_eq
    have h1 : 1 < Nat.card (Subgroup.center P) := Finite.one_lt_card_iff_nontrivial.mpr hZnt
    rw [hk] at h1 ⊢
    rcases k with _ | k
    · simp at h1
    · exact dvd_pow_self p (Nat.succ_ne_zero k)
  obtain ⟨u, huord⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) p hdvd
  exact ⟨(u : P), u.2, by rw [Subgroup.orderOf_coe u, huord]⟩

private theorem centralizer_le_of_mem_of_orderOf_eq {s : ℕ} [Fact s.Prime] {M S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf s S M)
    (hC : ∀ x ∈ S, orderOf x = s → Subgroup.centralizer ({x} : Set G) ≤ M)
    {x : G} (hxM : x ∈ M) (hx : orderOf x = s) :
    Subgroup.centralizer ({x} : Set G) ≤ M := by
  have hxp : IsPGroup s (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨Q, hQ⟩ := (hxp.comap_subtype (K := M)).exists_le_sylow
  let T : Subgroup G := (Q : Subgroup M).map M.subtype
  have hT : CFSG.ABGLocalTools.IsSylowOf s T M := ⟨Q, rfl⟩
  have hxcomap : (⟨x, hxM⟩ : M) ∈ (Subgroup.zpowers x).comap M.subtype :=
    Subgroup.mem_comap.mpr (Subgroup.mem_zpowers x)
  have hxT : x ∈ T := ⟨⟨x, hxM⟩, hQ hxcomap, rfl⟩
  obtain ⟨m, hmM, hmconj⟩ := hS.exists_mem_conj hT
  have hyS : m⁻¹ * x * m ∈ S := (hmconj x).mp hxT
  have hyord : orderOf (m⁻¹ * x * m) = s := by
    have h := MulEquiv.orderOf_eq (MulAut.conj m⁻¹) x
    simpa [MulAut.conj_apply] using h.trans hx
  have hyC : Subgroup.centralizer ({(m⁻¹ * x * m)} : Set G) ≤ M := hC _ hyS hyord
  intro z hz
  have hzC : m⁻¹ * z * m ∈ Subgroup.centralizer ({(m⁻¹ * x * m)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzx : z * x = x * z := Subgroup.mem_centralizer_singleton_iff.mp hz
    calc (m⁻¹ * z * m) * (m⁻¹ * x * m) = m⁻¹ * (z * x) * m := by group
      _ = m⁻¹ * (x * z) * m := by rw [hzx]
      _ = (m⁻¹ * x * m) * (m⁻¹ * z * m) := by group
  have hzM : m⁻¹ * z * m ∈ M := hyC hzC
  have hzEq : z = m * (m⁻¹ * z * m) * m⁻¹ := by group
  rw [hzEq]
  exact M.mul_mem (M.mul_mem hmM hzM) (M.inv_mem hmM)

private theorem normalizer_le_of_le_sylow {s : ℕ} [Fact s.Prime] {M S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf s S M) (hNS : Subgroup.normalizer (S : Set G) ≤ M)
    (hC : ∀ x ∈ M, orderOf x = s → Subgroup.centralizer ({x} : Set G) ≤ M) :
    ∀ Q : Subgroup G, Q ≠ ⊥ → IsPGroup s Q → Q ≤ S →
      Subgroup.normalizer (Q : Set G) ≤ M := by
  intro Q₀ hQ₀1 hQ₀p hQ₀S
  let P : ℕ → Prop := fun n => ∀ Q : Subgroup G, Q ≠ ⊥ → IsPGroup s Q → Q ≤ S →
    Nat.card S - Nat.card Q = n → Subgroup.normalizer (Q : Set G) ≤ M
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro Q hQ1 hQp hQS hcard
      by_cases hQS' : Q = S
      · rw [hQS']
        exact hNS
      · have hQlt : Q < S := lt_of_le_of_ne hQS hQS'
        have hTlt : Q < S ⊓ Subgroup.normalizer (Q : Set G) :=
          pGroup_proper_subgroup_lt_internal_normalizer s (Fact.out : s.Prime) S Q
            hS.isPGroup hQlt
        have hTp : IsPGroup s ↥(S ⊓ Subgroup.normalizer (Q : Set G)) :=
          hS.isPGroup.to_inf_left
        have hTle : S ⊓ Subgroup.normalizer (Q : Set G) ≤
            M ⊓ Subgroup.normalizer (Q : Set G) :=
          le_inf (inf_le_left.trans hS.le) inf_le_right
        obtain ⟨R, hTR, hRsyl⟩ := exists_isSylowOf_ge' (p := s) hTp hTle
        have hRM : R ≤ M := hRsyl.le.trans inf_le_left
        have hRN : R ≤ Subgroup.normalizer (Q : Set G) := hRsyl.le.trans inf_le_right
        obtain ⟨R', hRR', hR'syl⟩ := exists_isSylowOf_ge' (p := s) hRsyl.isPGroup hRM
        obtain ⟨m, hmM, hmconj⟩ := hS.exists_mem_conj hR'syl
        let Q₁ : Subgroup G := Q.map (MulAut.conj m⁻¹).toMonoidHom
        let T₁ : Subgroup G := R.map (MulAut.conj m⁻¹).toMonoidHom
        have hQT : Q ≤ R := hTlt.le.trans hTR
        have hQ₁T₁ : Q₁ ≤ T₁ := Subgroup.map_mono hQT
        have hT₁S : T₁ ≤ S := by
          rintro _ ⟨r, hr, rfl⟩
          simpa [MulAut.conj_apply] using (hmconj r).mp (hRR' hr)
        have hQ₁ne : Q₁ ≠ ⊥ :=
          (Subgroup.map_eq_bot_iff_of_injective Q (MulAut.conj m⁻¹).injective).not.mpr hQ1
        have hT₁ne : T₁ ≠ ⊥ := by
          intro h
          exact hQ₁ne (le_bot_iff.mp (h ▸ hQ₁T₁))
        have hT₁p : IsPGroup s T₁ := hS.isPGroup.to_le hT₁S
        have hcardQ : Nat.card Q₁ = Nat.card Q :=
          Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective
        have hcardR : Nat.card T₁ = Nat.card R :=
          Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective
        have hQltR : Nat.card Q < Nat.card R :=
          (Subgroup.card_lt_of_lt hTlt).trans_le (Subgroup.card_le_of_le hTR)
        have hcardQT : Nat.card Q₁ < Nat.card T₁ := by
          rw [hcardQ, hcardR]
          exact hQltR
        have hT₁card : Nat.card T₁ ≤ Nat.card S := Subgroup.card_le_of_le hT₁S
        have hlt : Nat.card S - Nat.card T₁ < n := by
          omega
        have hIH : Subgroup.normalizer (T₁ : Set G) ≤ M :=
          ih (Nat.card S - Nat.card T₁) hlt T₁ hT₁ne hT₁p hT₁S rfl
        have hMmap : M.map (MulAut.conj m⁻¹).toMonoidHom = M := by
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            simpa [MulAut.conj_apply] using
              M.mul_mem (M.mul_mem (M.inv_mem hmM) hy) hmM
          · intro hx
            refine ⟨m * x * m⁻¹, M.mul_mem (M.mul_mem hmM hx) (M.inv_mem hmM), ?_⟩
            change (MulAut.conj m⁻¹) (m * x * m⁻¹) = x
            rw [MulAut.conj_apply]
            group
        have hmap : (M ⊓ Subgroup.normalizer (Q : Set G)).map
            (MulAut.conj m⁻¹).toMonoidHom = M ⊓ Subgroup.normalizer (Q₁ : Set G) := by
          rw [Subgroup.map_inf _ _ _ (MulAut.conj m⁻¹).injective,
            Subgroup.map_equiv_normalizer_eq Q (MulAut.conj m⁻¹), hMmap]
        have hcardNM : Nat.card ↥(M ⊓ Subgroup.normalizer (Q₁ : Set G)) =
            Nat.card ↥(M ⊓ Subgroup.normalizer (Q : Set G)) := by
          rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective]
        have hT₁N : T₁ ≤ Subgroup.normalizer (Q₁ : Set G) := by
          rw [← Subgroup.map_equiv_normalizer_eq Q (MulAut.conj m⁻¹)]
          exact Subgroup.map_mono hRN
        have hT₁syl : CFSG.ABGLocalTools.IsSylowOf s T₁ (M ⊓ Subgroup.normalizer (Q₁ : Set G)) := by
          refine CFSG.ABGLocalTools.isSylowOf_of_card (le_inf (hT₁S.trans hS.le) hT₁N) ?_
          rw [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective, hRsyl.card_eq,
            hcardNM]
        have hNQ₁ : Subgroup.normalizer (Q₁ : Set G) ≤ M := by
          intro g hg
          obtain ⟨u, huZ, huord⟩ := exists_mem_center_orderOf_eq' hT₁p hT₁ne
          have huordG : orderOf (u : G) = s := (Subgroup.orderOf_coe u).trans huord
          have huC : (u : G) ∈ Subgroup.centralizer (Q₁ : Set G) := by
            rw [Subgroup.mem_centralizer_iff]
            intro q hq
            have hcomm : q * (u : G) = (u : G) * q := by
              have h := Subgroup.mem_center_iff.mp huZ ⟨q, hQ₁T₁ hq⟩
              exact congrArg (fun w : T₁ => (w : G)) h
            exact hcomm
          have hu_g_cent : (MulAut.conj g) (u : G) ∈ Subgroup.centralizer (Q₁ : Set G) := by
            rw [Subgroup.mem_centralizer_iff]
            intro q hq
            have hq' : g⁻¹ * q * g ∈ Q₁ :=
              (Subgroup.mem_set_normalizer_iff''.mp hg q).mp hq
            have hcomm : (g⁻¹ * q * g) * (u : G) = (u : G) * (g⁻¹ * q * g) :=
              Subgroup.mem_centralizer_iff.mp huC (g⁻¹ * q * g) hq'
            calc q * ((MulAut.conj g) (u : G))
                = g * ((g⁻¹ * q * g) * (u : G)) * g⁻¹ := by
                  rw [MulAut.conj_apply]
                  group
              _ = g * ((u : G) * (g⁻¹ * q * g)) * g⁻¹ := by rw [hcomm]
              _ = ((MulAut.conj g) (u : G)) * q := by
                  rw [MulAut.conj_apply]
                  group
          have hQ₁p : IsPGroup s Q₁ := hQp.map (MulAut.conj m⁻¹).toMonoidHom
          have hQ₁M : Q₁ ≤ M := hQ₁T₁.trans (hT₁S.trans hS.le)
          have hu_gM : (MulAut.conj g) (u : G) ∈ M := by
            have hdvdQ₁ : s ∣ Nat.card Q₁ :=
              hQ₁p.card_eq_or_dvd.resolve_left fun h =>
                hQ₁ne (Subgroup.card_eq_one.mp h)
            obtain ⟨x₀, hx₀ord⟩ := exists_prime_orderOf_dvd_card' (G := Q₁) s hdvdQ₁
            have hx₀mem : (x₀ : G) ∈ Q₁ := x₀.2
            have hx₀ordG : orderOf (x₀ : G) = s := (Subgroup.orderOf_coe x₀).trans hx₀ord
            have hCx₀ : Subgroup.centralizer ({(x₀ : G)} : Set G) ≤ M :=
              hC (x₀ : G) (hQ₁M hx₀mem) hx₀ordG
            exact hCx₀ ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx₀mem))
              hu_g_cent)
          have hu_g_ord : orderOf ((MulAut.conj g) (u : G)) = s := by
            rw [MulEquiv.orderOf_eq, huordG]
          have hgT₁M : T₁.map (MulAut.conj g).toMonoidHom ≤ M := by
            intro y hy
            obtain ⟨t, ht, rfl⟩ := hy
            have htcomm : (t : G) * (u : G) = (u : G) * (t : G) := by
              have h := Subgroup.mem_center_iff.mp huZ ⟨t, ht⟩
              exact congrArg (fun w : T₁ => (w : G)) h
            have htcent : (MulAut.conj g) (t : G) ∈
                Subgroup.centralizer ({((MulAut.conj g) (u : G))} : Set G) := by
              rw [Subgroup.mem_centralizer_singleton_iff]
              calc ((MulAut.conj g) (t : G)) * ((MulAut.conj g) (u : G))
                  = (MulAut.conj g) ((t : G) * (u : G)) := by
                    rw [map_mul]
                _ = (MulAut.conj g) ((u : G) * (t : G)) := by rw [htcomm]
                _ = ((MulAut.conj g) (u : G)) * ((MulAut.conj g) (t : G)) := by
                    rw [map_mul]
            exact hC ((MulAut.conj g) (u : G)) hu_gM hu_g_ord htcent
          have hgT₁N : T₁.map (MulAut.conj g).toMonoidHom ≤
              Subgroup.normalizer (Q₁ : Set G) := by
            intro y hy
            obtain ⟨t, ht, rfl⟩ := hy
            exact (Subgroup.normalizer (Q₁ : Set G)).mul_mem
              ((Subgroup.normalizer (Q₁ : Set G)).mul_mem hg (hT₁N ht))
              ((Subgroup.normalizer (Q₁ : Set G)).inv_mem hg)
          have hgT₁syl : CFSG.ABGLocalTools.IsSylowOf s (T₁.map (MulAut.conj g).toMonoidHom)
              (M ⊓ Subgroup.normalizer (Q₁ : Set G)) := by
            refine CFSG.ABGLocalTools.isSylowOf_of_card (le_inf hgT₁M hgT₁N) ?_
            rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hT₁syl.card_eq]
          obtain ⟨h, hh, hhconj⟩ := hT₁syl.exists_mem_conj hgT₁syl
          have hmapEq : T₁.map (MulAut.conj g).toMonoidHom =
              T₁.map (MulAut.conj h).toMonoidHom := by
            ext x
            constructor
            · intro hx
              exact Subgroup.mem_map_equiv.mpr ((hhconj x).mp hx)
            · intro hx
              exact (hhconj x).mpr (Subgroup.mem_map_equiv.mp hx)
          have hNT : h⁻¹ * g ∈ Subgroup.normalizer (T₁ : Set G) := by
            rw [Subgroup.mem_normalizer_iff]
            intro t
            constructor
            · intro ht
              have hsymm : (MulAut.conj g).symm (g * t * g⁻¹) = t := by
                rw [MulAut.conj_symm_apply]
                group
              have hgt : g * t * g⁻¹ ∈ T₁.map (MulAut.conj g).toMonoidHom :=
                Subgroup.mem_map_equiv.mpr (by rw [hsymm]; exact ht)
              rw [hmapEq] at hgt
              have hh : h⁻¹ * (g * t * g⁻¹) * h ∈ T₁ := by
                simpa [MulAut.conj_symm_apply] using (Subgroup.mem_map_equiv.mp hgt)
              have hEq : (h⁻¹ * g) * t * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * t * g⁻¹) * h := by
                group
              rwa [hEq]
            · intro ht
              have hht : h⁻¹ * (g * t * g⁻¹) * h ∈ T₁ := by
                have hEq : h⁻¹ * (g * t * g⁻¹) * h =
                    (h⁻¹ * g) * t * (h⁻¹ * g)⁻¹ := by group
                rwa [hEq]
              have hgt : g * t * g⁻¹ ∈ T₁.map (MulAut.conj h).toMonoidHom :=
                Subgroup.mem_map_equiv.mpr (by
                  simpa [MulAut.conj_symm_apply] using hht)
              rw [← hmapEq] at hgt
              have hsymm : (MulAut.conj g).symm (g * t * g⁻¹) = t := by
                rw [MulAut.conj_symm_apply]
                group
              have hmem := Subgroup.mem_map_equiv.mp hgt
              rw [hsymm] at hmem
              exact hmem
          have hhm : h⁻¹ * g ∈ M := hIH hNT
          have hgM : g ∈ M := by
            have hmem := M.mul_mem hh.1 hhm
            have heq : h * (h⁻¹ * g) = g := by group
            rwa [heq] at hmem
          exact hgM
        intro g hg
        have hmem : (MulAut.conj m⁻¹) g ∈
            (Subgroup.normalizer (Q : Set G)).map (MulAut.conj m⁻¹).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hg
        rw [Subgroup.map_equiv_normalizer_eq Q (MulAut.conj m⁻¹)] at hmem
        have hgm : m⁻¹ * g * m ∈ M := by
          simpa [MulAut.conj_apply] using hNQ₁ hmem
        have hgEq : g = m * (m⁻¹ * g * m) * m⁻¹ := by group
        rw [hgEq]
        exact M.mul_mem (M.mul_mem hmM hgm) (M.inv_mem hmM)
  exact hP (Nat.card S - Nat.card Q₀) Q₀ hQ₀1 hQ₀p hQ₀S rfl

theorem normalizer_le_of_normalizer_sylow_le {s : ℕ} [Fact s.Prime] {M S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf s S M) (hNS : Subgroup.normalizer (S : Set G) ≤ M)
    (hC : ∀ x ∈ S, orderOf x = s → Subgroup.centralizer ({x} : Set G) ≤ M) :
    ∀ Q : Subgroup G, Q ≠ ⊥ → IsPGroup s Q → Q ≤ M →
      Subgroup.normalizer (Q : Set G) ≤ M := by
  have hCM : ∀ x ∈ M, orderOf x = s → Subgroup.centralizer ({x} : Set G) ≤ M :=
    fun x hxM hx => centralizer_le_of_mem_of_orderOf_eq hS hC hxM hx
  have hN : ∀ Q : Subgroup G, Q ≠ ⊥ → IsPGroup s Q → Q ≤ S →
      Subgroup.normalizer (Q : Set G) ≤ M :=
    normalizer_le_of_le_sylow hS hNS hCM
  intro Q hQ1 hQp hQM
  obtain ⟨T, hQT, hT⟩ := exists_isSylowOf_ge' (p := s) hQp hQM
  obtain ⟨m, hmM, hmconj⟩ := hS.exists_mem_conj hT
  let Q' : Subgroup G := Q.map (MulAut.conj m⁻¹).toMonoidHom
  have hQ'S : Q' ≤ S := by
    rintro _ ⟨q, hq, rfl⟩
    simpa [MulAut.conj_apply] using (hmconj q).mp (hQT hq)
  have hQ'1 : Q' ≠ ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective Q (MulAut.conj m⁻¹).injective).not.mpr hQ1
  have hQ'p : IsPGroup s Q' := hQp.map (MulAut.conj m⁻¹).toMonoidHom
  have hNQ' : Subgroup.normalizer (Q' : Set G) ≤ M := hN Q' hQ'1 hQ'p hQ'S
  intro g hg
  have hmem : (MulAut.conj m⁻¹) g ∈
      (Subgroup.normalizer (Q : Set G)).map (MulAut.conj m⁻¹).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hg
  rw [Subgroup.map_equiv_normalizer_eq Q (MulAut.conj m⁻¹)] at hmem
  have hgm : m⁻¹ * g * m ∈ M := by
    simpa [MulAut.conj_apply] using hNQ' hmem
  have hgEq : g = m * (m⁻¹ * g * m) * m⁻¹ := by group
  rw [hgEq]
  exact M.mul_mem (M.mul_mem hmM hgm) (M.inv_mem hmM)

theorem isStronglyPEmbedded_of_normalizer_sylow_le {s : ℕ} [Fact s.Prime] {M S : Subgroup G}
    (hM : M ≠ ⊤) (hS : CFSG.ABGLocalTools.IsSylowOf s S M) (hS1 : S ≠ ⊥)
    (hNS : Subgroup.normalizer (S : Set G) ≤ M)
    (hC : ∀ x ∈ S, orderOf x = s → Subgroup.centralizer ({x} : Set G) ≤ M) :
    IsStronglyPEmbedded s M := by
  have hsS : s ∣ Nat.card S :=
    hS.isPGroup.card_eq_or_dvd.resolve_left fun h => hS1 (Subgroup.card_eq_one.mp h)
  have hsM : s ∣ Nat.card M := hsS.trans (Subgroup.card_dvd_of_le hS.le)
  exact CFSG.LocalAnalysis.RankThreeUC.isStronglyPEmbedded_of_normalizer_le hM hsM
    (normalizer_le_of_normalizer_sylow_le hS hNS hC)

end CFSG.RankThree.PartOne
