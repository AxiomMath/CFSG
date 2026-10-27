module

public import CFSG.Quasithin.Background.C124BlkTop
public import CFSG.Quasithin.H13.A6S1372L74p

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L74

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_baum {X R U : Subgroup G} (hRX : R ≤ X) (hUe : IsElemAbelian 2 U)
    (hXU : X ≤ Subgroup.normalizer (U : Set G))
    (hCR : X ⊓ Subgroup.centralizer (U : Set G) ≤ R)
    {A : Subgroup (MulAut (IntMod U hUe))} (hAR : A ≤ autI hUe R)
    (hBA : autI hUe (baum R) ≤ A) {d : G} (hdX : d ∈ X)
    (hdA : convI hUe ⟨d, hXU hdX⟩ ∈ Subgroup.normalizer (A : Set (MulAut (IntMod U hUe)))) :
    d ∈ Subgroup.normalizer (baum R : Set G) := by
  set P : Subgroup G := (A.comap (convHom hUe X hXU)).map X.subtype with hPdef
  have hmemP : ∀ g, g ∈ P ↔ ∃ hg : g ∈ X, convI hUe ⟨g, hXU hg⟩ ∈ A := by
    intro g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hg, h⟩
      exact ⟨⟨g, hg⟩, h, rfl⟩
  have hPR : P ≤ R := by
    intro g hg
    obtain ⟨hgX, hgA⟩ := (hmemP g).1 hg
    obtain ⟨r, hr, hrg⟩ := (mem_autI hUe).1 (hAR hgA)
    have h1 : convI hUe (r⁻¹ * ⟨g, hXU hgX⟩) = 1 := by
      rw [map_mul, map_inv, hrg, inv_mul_cancel]
    have h2 := (convI_eq_one_iff hUe _).1 h1
    have h3 : (r : G)⁻¹ * g ∈ R :=
      hCR ⟨X.mul_mem (X.inv_mem (hRX hr)) hgX, by simpa using h2⟩
    have e : g = (r : G) * ((r : G)⁻¹ * g) := by group
    rw [e]
    exact R.mul_mem hr h3
  have hBP : baum R ≤ P := fun b hb =>
    (hmemP b).2 ⟨hRX (B2F.baum_le R hb), hBA (convI_mem_autI hUe hb _)⟩
  have heq : baum R = baum P := baum_eq_of_le hBP hPR
  have hdP : d ∈ Subgroup.normalizer (P : Set G) := by
    refine A6L19.mem_normalizer_of_conj fun g hg => ?_
    obtain ⟨hgX, hgA⟩ := (hmemP g).1 hg
    refine (hmemP _).2 ⟨X.mul_mem (X.mul_mem hdX hgX) (X.inv_mem hdX), ?_⟩
    have e : (⟨d * g * d⁻¹, hXU (X.mul_mem (X.mul_mem hdX hgX) (X.inv_mem hdX))⟩ :
        ↥(Subgroup.normalizer (U : Set G))) = ⟨d, hXU hdX⟩ * ⟨g, hXU hgX⟩ * ⟨d, hXU hdX⟩⁻¹ :=
      Subtype.ext rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hdA _).mp hgA
  rw [heq]
  exact normalizer_le_normalizer_baum P hdP

theorem exists_lift_three {K U : Subgroup G} (hUe : IsElemAbelian 2 U)
    (hCK : K ⊓ Subgroup.centralizer (U : Set G) = pCoreOf 2 K)
    {δ : MulAut (IntMod U hUe)} (hδ : δ ∈ autI hUe K) (hδ3 : δ ^ 3 = 1) (hδ1 : δ ≠ 1) :
    ∃ d ∈ K, d ^ 3 = 1 ∧ d ≠ 1 ∧ ∃ hd : d ∈ Subgroup.normalizer (U : Set G),
      convI hUe ⟨d, hd⟩ ∈ Subgroup.zpowers δ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, rfl⟩ := (mem_autI hUe).1 hδ
  have h1 : convI hUe (k ^ 3) = 1 := by rw [map_pow, hδ3]
  have h2 : (k : G) ^ 3 ∈ pCoreOf 2 K := by
    rw [← hCK]
    exact ⟨K.pow_mem hk 3, by simpa using (convI_eq_one_iff hUe _).1 h1⟩
  obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 K ⟨_, h2⟩
  have hb' : ((k : G) ^ 3) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  refine ⟨(k : G) ^ 2 ^ b, K.pow_mem hk _, ?_, ?_, (Subgroup.normalizer _).pow_mem k.2 _, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hb']
  · intro hd
    apply hδ1
    have h3 : convI hUe k ^ 2 ^ b = 1 := by
      rw [← map_pow]
      have : k ^ 2 ^ b = 1 := Subtype.ext (by simpa using hd)
      rw [this, map_one]
    have h6 : orderOf (convI hUe k) ∣ Nat.gcd 3 (2 ^ b) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hδ3) (orderOf_dvd_of_pow_eq_one h3)
    have h7 : Nat.gcd 3 (2 ^ b) = 1 := Nat.Coprime.pow_right _ (by norm_num)
    rw [h7, Nat.dvd_one, orderOf_eq_one_iff] at h6
    exact h6
  · have e' : (⟨(k : G) ^ 2 ^ b, (Subgroup.normalizer _).pow_mem k.2 _⟩ :
        ↥(Subgroup.normalizer (U : Set G))) = k ^ 2 ^ b := Subtype.ext (by simp)
    rw [e', map_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

omit [Finite G] in
theorem commV_autI_eq_top_of_commutator {K U : Subgroup G} (hUe : IsElemAbelian 2 U)
    (hKU : K ≤ Subgroup.normalizer (U : Set G)) (hUK : ⁅U, K⁆ = U) :
    commV (autI hUe K) = ⊤ :=
  CFSG.Quasithin.C124.commV_autI_eq_top hUe hKU hUK

omit [Finite G] in
theorem nonempty_mulEquiv_autI {K U : Subgroup G} (hUe : IsElemAbelian 2 U)
    (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hCK : K ⊓ Subgroup.centralizer (U : Set G) = pCoreOf 2 K) :
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥(autI hUe K)) := by
  have hker : (convHom hUe K hKU).ker = CFSG.pCore 2 ↥K := by
    rw [ker_convHom, hCK]
    ext k
    rw [Subgroup.mem_subgroupOf]
    exact mem_pCoreOf_iff k
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange _).trans
      (MulEquiv.subgroupCongr (range_convHom hUe K hKU)))⟩

theorem sqtkGroup_autI {H K U : Subgroup G} (hUe : IsElemAbelian 2 U) (hS : SQTKGroup ↥H)
    (hKH : K ≤ H) (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hCK : K ⊓ Subgroup.centralizer (U : Set G) = pCoreOf 2 K) :
    SQTKGroup ↥(autI hUe K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSK : SQTKGroup ↥K := by
    have h1 := InternalSec.sqtkGroup_subgroup hS (K.subgroupOf H)
    refine InternalSec.sqtkGroup_of_surjective (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hKH).surjective ?_ h1
    rw [(MonoidHom.ker_eq_bot_iff _).mpr (Subgroup.subgroupOfEquivOfLe hKH).injective]
    exact IsPGroup.of_bot
  set f : ↥K →* ↥(autI hUe K) := (MulEquiv.subgroupCongr (range_convHom hUe K hKU)).toMonoidHom.comp
    (convHom hUe K hKU).rangeRestrict with hf
  have hfs : Function.Surjective f :=
    (MulEquiv.subgroupCongr (range_convHom hUe K hKU)).surjective.comp
      (MonoidHom.rangeRestrict_surjective _)
  refine InternalSec.sqtkGroup_of_surjective f hfs ?_ hSK
  rintro ⟨x, hx⟩
  have h1 : convHom hUe K hKU x = 1 := by
    have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    simpa [hf] using h
  rw [convHom_apply, convI_eq_one_iff] at h1
  have h2 : (x : G) ∈ pCoreOf 2 K := by
    rw [← hCK]
    exact ⟨x.2, h1⟩
  obtain ⟨n, hn⟩ := pCoreOf_isPGroup 2 K ⟨_, h2⟩
  refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg Subtype.val hn
  simpa using this

theorem inf_centralizer_autI_eq_bot {K R U : Subgroup G} (hUe : IsElemAbelian 2 U)
    (hR : IsPGroup 2 R) (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hred : IsTwoReducedIn (K ⊔ R) U)
    (hZ : ∀ φ ∈ autI hUe K, (∀ ψ ∈ autI hUe K, φ * ψ = ψ * φ) → φ = 1) :
    autI hUe (K ⊔ R) ⊓ Subgroup.centralizer (autI hUe K : Set (MulAut (IntMod U hUe))) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXU : K ⊔ R ≤ Subgroup.normalizer (U : Set G) := hred.2.1
  have hXK : K ⊔ R ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hRK
  have hΓK : autI hUe (K ⊔ R) ≤
      Subgroup.normalizer (autI hUe K : Set (MulAut (IntMod U hUe))) := by
    intro γ hγ
    obtain ⟨g, hg, rfl⟩ := (mem_autI hUe).1 hγ
    refine A6L19.mem_normalizer_of_conj fun φ hφ => ?_
    exact convI_conj_mem hUe g.2 (hXK hg) hφ
  have hY2 : IsPGroup 2 ↥(autI hUe (K ⊔ R) ⊓
      Subgroup.centralizer (autI hUe K : Set (MulAut (IntMod U hUe)))) := by
    rintro ⟨y, hyΓ, hyC⟩
    obtain ⟨g, hg, rfl⟩ := (mem_autI hUe).1 hyΓ
    obtain ⟨a, ha⟩ := exists_two_pow_mem_of_mem_sup hR hRK hg
    have h1 : convI hUe g ^ 2 ^ a ∈ autI hUe K := by
      rw [← map_pow]
      exact (mem_autI hUe).2 ⟨_, by simpa using ha, rfl⟩
    have h2 : convI hUe g ^ 2 ^ a = 1 := hZ _ h1 fun ψ hψ =>
      ((Subgroup.centralizer _).pow_mem hyC (2 ^ a) |> Subgroup.mem_centralizer_iff.mp) ψ hψ
        |>.symm
    exact ⟨a, Subtype.ext (by simpa using h2)⟩
  refine B2F.eq_bot_of_normal_isPGroup hUe hred inf_le_left ?_ hY2
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun γ hγ =>
    mem_normalizer_inf_of (Subgroup.le_normalizer hγ)
      (InternalSec.le_normalizer_centralizer hΓK hγ)

end A6L74

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

theorem not_thompsonJ_le_of_eq (h1227 : U3.Stmt13_2_2_7) (hhat : ¬ IsHatA6 L)
    (hB : ¬ H13.IsA6Block L) {K : Subgroup G} (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G))
    {U : Subgroup G} (hUe : IsElemAbelian 2 U) (hUR : U ≤ pCoreOf 2 (S.L1 ⊔ T))
    (hRC : pCoreOf 2 (S.L1 ⊔ T) ⊓ Subgroup.centralizer (U : Set G) =
      pCoreOf 2 (K ⊔ pCoreOf 2 (S.L1 ⊔ T))) :
    ¬ thompsonJ (pCoreOf 2 (S.L1 ⊔ T)) ≤ Subgroup.centralizer (U : Set G) := by
  intro hJ
  have hbaum : baum (pCoreOf 2 (S.L1 ⊔ T)) = baum (pCoreOf 2 (K ⊔ pCoreOf 2 (S.L1 ⊔ T))) := by
    rw [← hRC]
    exact baum_eq_baum_centralizer hUe hUR (le_inf (thompsonJ_le_self _) hJ)
  have hRM : Subgroup.normalizer (baum (pCoreOf 2 (S.L1 ⊔ T)) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
    rcases h1227 G T L V S.L1 S.h13 S.irr S.zv (fun h => absurd h hhat) (fun _ => rfl) S.a6
      with h | h
    · exact normalizer_baum_R1_le_M h
    · exact absurd h hB
  apply hKM
  intro k hk
  apply hRM
  rw [hbaum]
  exact normalizer_le_normalizer_baum _ (le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hk))

section Sylow

variable {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hKH : K ≤ H)
  (hHK : H ≤ Subgroup.normalizer (K : Set G))
  (hKL1 : ∀ k ∈ K, ∀ l ∈ S.L1, k * l * k⁻¹ * l⁻¹ ∈ pCoreOf 2 K)
include hH hKH hHK hKL1

theorem T_inf_le_R1 : T ⊓ K ≤ pCoreOf 2 (S.L1 ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hOQ : pCoreOf 2 K ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKH)
      (hHK.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
  have hOT : pCoreOf 2 K ≤ T := hOQ.trans (pCoreOf_le_of_sylow S.h13.sylow hTH)
  have hL1N : S.L1 ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    intro l hl
    refine A6L19.mem_normalizer_of_conj fun x hx => ⟨?_, ?_⟩
    · have h1 := hKL1 x hx.2 l⁻¹ (S.L1.inv_mem hl)
      have hlO : l ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
        normalizer_le_normalizer_pCoreOf 2 K (hHK (hL1H hl))
      have h2 := (Subgroup.mem_normalizer_iff.mp hlO _).mp h1
      have e : l * x * l⁻¹ = (l * (x * l⁻¹ * x⁻¹ * l⁻¹⁻¹) * l⁻¹) * x := by group
      rw [e]
      exact T.mul_mem (hOT h2) hx.1
    · exact (Subgroup.mem_normalizer_iff.mp (hHK (hL1H hl)) x).mp hx.2
  have hTN : T ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_inf_of (Subgroup.le_normalizer ht) (hHK (hTH ht))
  exact le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right) (sup_le hL1N hTN)
    (S.h13.sylow.1.to_inf_left)

theorem isSylowTwoOf_R1_simple :
    IsSylowTwoOf (pCoreOf 2 (S.L1 ⊔ T)) (K ⊔ pCoreOf 2 (S.L1 ⊔ T)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  obtain ⟨-, hRK⟩ := pCoreOf_le_R1_and hH hKH hHK
  have hR2 : IsPGroup 2 (pCoreOf 2 (S.L1 ⊔ T)) := pCoreOf_isPGroup 2 _
  have hTs : IsSylowTwoOf T H :=
    ⟨hTH, S.h13.sylow.1, fun h => S.h13.sylow.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hTH))⟩
  have hTK : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hTs hKH hHK
  have hle : T ⊓ K ≤ pCoreOf 2 (S.L1 ⊔ T) ⊓ K := le_inf (T_inf_le_R1 hH hKH hHK hKL1) inf_le_right
  have hRKs : IsSylowTwoOf (pCoreOf 2 (S.L1 ⊔ T) ⊓ K) K := by
    refine ⟨inf_le_right, hR2.to_inf_left, fun h => hTK.2.2 ?_⟩
    show 2 ∣ (T ⊓ K).relIndex K
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ hle inf_le_right]
    exact Dvd.dvd.mul_left (show 2 ∣ (pCoreOf 2 (S.L1 ⊔ T) ⊓ K).relIndex K from h) _
  rw [A4.isSylowTwoOf_iff_maximal]
  refine ⟨le_sup_right, hR2, fun P hPX hP hRP y hy => ?_⟩
  have hyX := hPX hy
  rw [sup_comm] at hyX
  obtain ⟨r, hr, k, hk, rfl⟩ := (A6L19.mem_sup_iff hRK).1 hyX
  have hkP : k ∈ P := by
    have e : k = r⁻¹ * (r * k) := by group
    rw [e]
    exact P.mul_mem (P.inv_mem (hRP hr)) hy
  have hmax := (A4.isSylowTwoOf_iff_maximal.mp hRKs).2.2 (P ⊓ K) inf_le_right hP.to_inf_left
    (inf_le_inf_right K hRP)
  exact (pCoreOf 2 (S.L1 ⊔ T)).mul_mem hr (hmax ⟨hkP, hk⟩).1

end Sylow

end Setting4

end CFSG.Quasithin.H13.A6
