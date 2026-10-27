module

public import CFSG.Quasithin.Background.G2A5Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.A5Model
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

namespace A5SettingCore

variable [Finite G] {V V₁ L T H : Subgroup G} (S : A5SettingCore V V₁ L T H)

include S

theorem exists_inf_of_K4 {k : A5} (hk : k ∈ K4) :
    ∃ x : L, (x : G) ∈ conjClosure V H ∧ S.D.θ x = k := by
  obtain ⟨k', hk'K, hkk'⟩ := K4_comm_cover k hk
  rw [← S.Ubar_eq_K4] at hk'K
  obtain ⟨u₀, hu₀⟩ := hk'K
  obtain ⟨a, ha1, haθ⟩ := S.D.exists_l1_of_odd (le_conjClosure V₁ L) S.D.line c3A c3A_mem c3A_pow
  have haH : (a : G) ∈ H :=
    S.hyp.base.lOne_sup_le ((le_sup_left : lOne L V₁ ≤ lOne L V₁ ⊔ T) ha1)
  have haN : (a : G) ∈ Subgroup.normalizer (conjClosure V H : Set G) :=
    le_normalizer_conjClosure V H haH
  have hu₀N : (u₀ : G) ∈ Subgroup.normalizer (L : Set G) := S.U_le_normL u₀.2
  have hxU : (u₀ : G) * a * (u₀ : G)⁻¹ * (a : G)⁻¹ ∈ conjClosure V H := by
    have h1 : (a : G) * (u₀ : G)⁻¹ * (a : G)⁻¹ ∈ conjClosure V H :=
      (Subgroup.mem_normalizer_iff.1 haN _).1 (inv_mem u₀.2)
    have := Subgroup.mul_mem _ u₀.2 h1
    simpa [mul_assoc] using this
  have hxL : (u₀ : G) * a * (u₀ : G)⁻¹ * (a : G)⁻¹ ∈ L := by
    have h1 : (u₀ : G) * a * (u₀ : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hu₀N _).1 a.2
    exact L.mul_mem h1 (L.inv_mem a.2)
  refine ⟨⟨_, hxL⟩, hxU, ?_⟩
  have hu₀' : (u₀ : G) ∈ L ⊔ conjClosure V H :=
    (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) u₀.2
  have ha' : (a : G) ∈ L ⊔ conjClosure V H := (le_sup_left : L ≤ L ⊔ conjClosure V H) a.2
  have e : (⟨(u₀ : G) * a * (u₀ : G)⁻¹ * (a : G)⁻¹,
      (le_sup_left : L ≤ L ⊔ conjClosure V H) hxL⟩ : ↥(L ⊔ conjClosure V H)) =
      ⟨u₀, hu₀'⟩ * ⟨a, ha'⟩ * ⟨u₀, hu₀'⟩⁻¹ * ⟨a, ha'⟩⁻¹ := Subtype.ext (by simp)
  have h1 := S.Phi_of_L ⟨_, hxL⟩
  rw [← h1, e, map_mul, map_mul, map_mul, map_inv, map_inv]
  have h2 : S.Phi ⟨u₀, hu₀'⟩ = k' := hu₀
  have h3 : S.Phi ⟨a, ha'⟩ = c3A := by rw [S.Phi_of_L a, haθ]
  rw [h2, h3, hkk']

theorem odd_index_ker_sup :
    ¬ 2 ∣ (S.D.θ.ker ⊔ ((L ⊓ conjClosure V H).subgroupOf L)).index := by
  have key := Subgroup.index_map ((L ⊓ conjClosure V H).subgroupOf L) S.D.θ
  have hrange : S.D.θ.range = ⊤ := MonoidHom.range_eq_top.2 S.D.surj
  have hmap : ((L ⊓ conjClosure V H).subgroupOf L).map S.D.θ = K4 := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hx' := Subgroup.mem_subgroupOf.1 hx
      rw [← S.Phi_of_L x]
      exact S.betaU_mem_K4 ⟨x, hx'.2⟩
    · intro k hk
      obtain ⟨x, hxU, hx⟩ := S.exists_inf_of_K4 hk
      exact ⟨x, Subgroup.mem_subgroupOf.2 ⟨x.2, hxU⟩, hx⟩
  rw [hmap, hrange, Subgroup.index_top, mul_one] at key
  rw [sup_comm, ← key]
  exact K4_index_odd

theorem inf_pCoreOf_eq_ker {I : Subgroup G} (hI' : I = L ⊔ conjClosure V H) :
    (L ⊓ pCoreOf 2 I).subgroupOf L = S.D.θ.ker := by
  obtain ⟨hIle, hSxO, -, -, -⟩ := sx_facts_gen hI' S.U_le_T S.hyp.G22_three.2
    S.hyp.base.T_le_normL S.hyp.base.sylow_LT
  have hLI : L ≤ I := hI' ▸ le_sup_left
  rw [S.D.ker_eq]
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · rintro ⟨_, hx⟩
    exact hSxO hx
  · intro hx
    exact ⟨x.2, mem_pCoreOf_of_mem_pCoreOf_of_le hIle (hLI x.2) hx⟩

theorem L_inf_le_P {U I : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g) :
    L ⊓ pCoreOf 2 I ≤ (U ⊓ pCoreOf 2 I) ⊔ rconj (U ⊓ pCoreOf 2 I) g := by
  subst hU
  have hI' : I = L ⊔ conjClosure V H := hI.trans (S.G24_two_aux hg hgN)
  obtain ⟨hIle, hSxO, hSxT, hINorm, hSxU⟩ := sx_facts_gen hI' S.U_le_T
    S.hyp.G22_three.2 S.hyp.base.T_le_normL S.hyp.base.sylow_LT
  have hLI : L ≤ I := hI' ▸ le_sup_left
  have hgI : g ∈ I := hLI hg
  have hIP := I_le_normalizer_P hI hgI hINorm hSxU
  have hPSx : (conjClosure V H ⊓ pCoreOf 2 I) ⊔ rconj (conjClosure V H ⊓ pCoreOf 2 I) g ≤
      pCoreOf 2 I := sup_le inf_le_right (rconj_inf_le_Sx hgI hINorm)
  set P := (conjClosure V H ⊓ pCoreOf 2 I) ⊔ rconj (conjClosure V H ⊓ pCoreOf 2 I) g with hP
  refine inf_le_of_central_odd_index (C := L ⊓ conjClosure V H) S.hyp.base.oTwo_eq hPSx
    (hLI.trans hIP) ?_ ((pCoreOf_isPGroup 2 I).to_le inf_le_right) ?_ ?_
  · intro k hk y hy
    have := P.inv_mem (comm_Sx_mem_P hI hgI hINorm hSxU (hLI hy) hk.2)
    simpa [mul_assoc] using this
  · intro x hx
    exact (le_sup_left : conjClosure V H ⊓ pCoreOf 2 I ≤ P) ⟨hx.2.2, hx.1.2⟩
  · rw [S.inf_pCoreOf_eq_ker hI']
    exact S.odd_index_ker_sup

theorem exists_inf_mul_mem {u : G} (hu : u ∈ conjClosure V H) :
    ∃ x : L, (x : G) ∈ conjClosure V H ∧ (x : G)⁻¹ * u ∈ pCoreOf 2 (L ⊔ T) := by
  obtain ⟨x, hxU, hx⟩ := S.exists_inf_of_K4 (S.betaU_mem_K4 ⟨u, hu⟩)
  refine ⟨x, hxU, ?_⟩
  have hxLU : (x : G) ∈ L ⊔ conjClosure V H := (le_sup_left : L ≤ L ⊔ conjClosure V H) x.2
  have huLU : u ∈ L ⊔ conjClosure V H :=
    (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) hu
  have e : (⟨(x : G)⁻¹ * u, Subgroup.mul_mem _ (inv_mem hxLU) huLU⟩ :
      ↥(L ⊔ conjClosure V H)) = ⟨x, hxLU⟩⁻¹ * ⟨u, huLU⟩ := Subtype.ext (by simp)
  have h1 : S.Phi ⟨(x : G)⁻¹ * u, Subgroup.mul_mem _ (inv_mem hxLU) huLU⟩ = 1 := by
    rw [e, map_mul, map_inv, S.Phi_of_L x]
    have : S.Phi ⟨u, huLU⟩ = S.betaU ⟨u, hu⟩ := rfl
    rw [this, hx, inv_mul_cancel]
  exact (S.Phi_eq_one_iff _).1 h1

theorem pCoreOf_I_le_P {U I : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g) :
    pCoreOf 2 I ≤ (U ⊓ pCoreOf 2 I) ⊔ rconj (U ⊓ pCoreOf 2 I) g := by
  have hL := S.L_inf_le_P hU hg hgN hI
  subst hU
  have hI' : I = L ⊔ conjClosure V H := hI.trans (S.G24_two_aux hg hgN)
  obtain ⟨hIle, hSxO, hSxT, hINorm, hSxU⟩ := sx_facts_gen hI' S.U_le_T
    S.hyp.G22_three.2 S.hyp.base.T_le_normL S.hyp.base.sylow_LT
  have hLI : L ≤ I := hI' ▸ le_sup_left
  have hUI : conjClosure V H ≤ I := hI' ▸ le_sup_right
  set P := (conjClosure V H ⊓ pCoreOf 2 I) ⊔ rconj (conjClosure V H ⊓ pCoreOf 2 I) g with hP
  have hWP : conjClosure V H ⊓ pCoreOf 2 I ≤ P := le_sup_left
  have hmul : ((L ⊔ conjClosure V H : Subgroup G) : Set G) =
      (L : Set G) * (conjClosure V H : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L _ (fun u hu => S.U_le_normL hu)
  intro s hs
  have hsLU : s ∈ L ⊔ conjClosure V H := hI' ▸ pCoreOf_le 2 I hs
  rw [SetLike.mem_coe.symm, hmul] at hsLU
  obtain ⟨l, hl, u, hu, rfl⟩ := hsLU
  change l * u ∈ pCoreOf 2 I at hs
  show l * u ∈ P
  obtain ⟨x, hxU, hx⟩ := S.exists_inf_mul_mem hu
  have hxI : (x : G) ∈ I := hLI x.2
  have hwI : (x : G)⁻¹ * u ∈ I := Subgroup.mul_mem _ (inv_mem hxI) (hUI hu)
  have hwSx : (x : G)⁻¹ * u ∈ pCoreOf 2 I := mem_pCoreOf_of_mem_pCoreOf_of_le hIle hwI hx
  have hwP : (x : G)⁻¹ * u ∈ P := hWP ⟨Subgroup.mul_mem _ (inv_mem hxU) hu, hwSx⟩
  have hlxSx : l * (x : G) ∈ pCoreOf 2 I := by
    have := Subgroup.mul_mem _ hs (Subgroup.inv_mem _ hwSx)
    simpa [mul_assoc] using this
  have hlxP : l * (x : G) ∈ P := hL ⟨L.mul_mem hl x.2, hlxSx⟩
  have := P.mul_mem hlxP hwP
  simpa [mul_assoc] using this

theorem pCoreOf_I_eq {U I : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g) :
    pCoreOf 2 I = (U ⊓ pCoreOf 2 I) ⊔ rconj (U ⊓ pCoreOf 2 I) g ∧
      ((pCoreOf 2 I : Subgroup G) : Set G) =
        ((U ⊓ pCoreOf 2 I : Subgroup G) : Set G) *
          ((rconj (U ⊓ pCoreOf 2 I) g : Subgroup G) : Set G) := by
  have hle := S.pCoreOf_I_le_P hU hg hgN hI
  subst hU
  have hI' : I = L ⊔ conjClosure V H := hI.trans (S.G24_two_aux hg hgN)
  obtain ⟨hIle, hSxO, hSxT, hINorm, hSxU⟩ := sx_facts_gen hI' S.U_le_T
    S.hyp.G22_three.2 S.hyp.base.T_le_normL S.hyp.base.sylow_LT
  have hLI : L ≤ I := hI' ▸ le_sup_left
  exact pCoreOf_I_eq_of_le hI (hLI hg) hINorm hSxU hle

end A5SettingCore

namespace AlmostSpecialA5Core

variable [Finite G] {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialA5Core V V₁ L T H)

include hyp

theorem G24_three {U I S W : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g)
    (hS : S = pCoreOf 2 I) (hW : W = U ⊓ S) :
    S = W ⊔ rconj W g ∧ (S : Set G) = (W : Set G) * (rconj W g : Set G) := by
  obtain ⟨D⟩ := hyp.natural.nonempty_natData5 hyp.base.le_V (le_conjClosure V₁ L) hyp.card_V₁
    hyp.V_eq
  let St : A5SettingCore V V₁ L T H := ⟨hyp, D⟩
  subst hS
  subst hW
  exact St.pCoreOf_I_eq hU hg hgN hI

end AlmostSpecialA5Core

namespace AlmostSpecialA5Hyp

variable [Finite G] {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialA5Hyp V V₁ L T H)

include hyp

theorem G24_three {U I S W : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g)
    (hS : S = pCoreOf 2 I) (hW : W = U ⊓ S) :
    S = W ⊔ rconj W g ∧ (S : Set G) = (W : Set G) * (rconj W g : Set G) :=
  hyp.toCore.G24_three hU hg hgN hI hS hW

end AlmostSpecialA5Hyp

end CFSG.Quasithin
