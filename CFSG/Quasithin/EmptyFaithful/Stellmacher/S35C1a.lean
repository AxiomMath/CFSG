module

public import CFSG.Quasithin.Background.F7Basic
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace F53.Stellmacher

namespace S35

namespace C1

theorem le_of_le_sup_commutator_top {K : Type} [Group K] [Group.IsNilpotent K]
    (N V : Subgroup K) [N.Normal] (h : V ≤ N ⊔ ⁅V, ⊤⁆) : V ≤ N := by
  set f : K →* K ⧸ N := QuotientGroup.mk' N with hf
  have hker : f.ker = N := QuotientGroup.ker_mk' N
  have h1 : V.map f ≤ ⁅V.map f, (⊤ : Subgroup (K ⧸ N))⁆ := by
    have h2 : V ≤ Subgroup.comap f ⁅V.map f, (⊤ : Subgroup (K ⧸ N))⁆ := by
      have : Subgroup.comap f ⁅V.map f, (⊤ : Subgroup (K ⧸ N))⁆ = ⁅V, (⊤ : Subgroup K)⁆ ⊔ N := by
        have e : ⁅V.map f, (⊤ : Subgroup (K ⧸ N))⁆ = Subgroup.map f ⁅V, (⊤ : Subgroup K)⁆ := by
          rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective f QuotientGroup.mk_surjective]
        rw [e, Subgroup.comap_map_eq, hker]
      rw [this, sup_comm]
      exact h
    exact Subgroup.map_le_iff_le_comap.mpr h2
  have h3 : ∀ n, V.map f ≤ Subgroup.lowerCentralSeries (⊤ : Subgroup (K ⧸ N)) n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih => exact h1.trans (Subgroup.commutator_mono ih le_rfl)
  obtain ⟨n, hn⟩ := (Subgroup.nilpotent_iff_lowerCentralSeries (G := K ⧸ N)).mp inferInstance
  have h4 := h3 n
  rw [hn, le_bot_iff] at h4
  intro x hx
  have : f x = 1 := by
    have hx' : f x ∈ V.map f := ⟨x, hx, rfl⟩
    rw [h4] at hx'
    simpa using hx'
  rwa [← hker]

open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_le_left_of_le_normalizer {V L : Subgroup G}
    (hL : L ≤ Subgroup.normalizer (V : Set G)) : ⁅V, L⁆ ≤ V := by
  refine Subgroup.commutator_le.mpr fun v hv l hl => ?_
  have h := (Subgroup.mem_normalizer_iff.mp (hL hl) v⁻¹).mp (V.inv_mem hv)
  have h2 := V.mul_mem hv h
  simpa [commutatorElement_def, mul_assoc] using h2

theorem mem_normalizer_commutator {V L : Subgroup G} {f : G}
    (hV : f ∈ Subgroup.normalizer (V : Set G)) (hL : f ∈ Subgroup.normalizer (L : Set G)) :
    f ∈ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
  have key : ∀ g : G, g ∈ Subgroup.normalizer (V : Set G) → g ∈ Subgroup.normalizer (L : Set G) →
      ∀ x ∈ ⁅V, L⁆, g * x * g⁻¹ ∈ ⁅V, L⁆ := by
    intro g hgV hgL
    have hle : ⁅V, L⁆ ≤ Subgroup.comap (MulAut.conj g).toMonoidHom ⁅V, L⁆ := by
      refine Subgroup.commutator_le.mpr fun v hv l hl => ?_
      have e : (MulAut.conj g).toMonoidHom ⁅v, l⁆ = ⁅g * v * g⁻¹, g * l * g⁻¹⁆ := by
        simp [commutatorElement_def]
        group
      rw [Subgroup.mem_comap, e]
      exact Subgroup.commutator_mem_commutator
        ((Subgroup.mem_normalizer_iff.mp hgV v).mp hv)
        ((Subgroup.mem_normalizer_iff.mp hgL l).mp hl)
    intro x hx
    have := hle hx
    simpa using this
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => key f hV hL x hx, fun hx => ?_⟩
  have := key f⁻¹ ((Subgroup.inv_mem_iff _).mpr hV) ((Subgroup.inv_mem_iff _).mpr hL) _ hx
  simpa [mul_assoc] using this

variable [Finite G]

theorem comm_oTwoRes_of_comm {F V : Subgroup G} (hFV : F ≤ Subgroup.normalizer (V : Set G))
    (hV2 : ∀ x ∈ V, x ^ 2 = 1) (hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (h : V ≤ ⁅V, F⁆) : V ≤ ⁅V, oTwoRes F⁆ := by
  obtain ⟨P, hP⟩ := exists_isSylowTwoOf F
  have hFLP : F ≤ oTwoRes F ⊔ P := le_oTwoRes_sup_of_isSylowTwoOf hP
  set L := oTwoRes F with hLdef
  set U : Subgroup G := ⁅V, L⁆ with hUdef
  have hPF : P ≤ F := hP.1
  have hLF : L ≤ F := oTwoRes_le F
  have hFL : ∀ f ∈ F, f ∈ Subgroup.normalizer (L : Set G) := fun f hf => le_normalizer_oTwoRes F hf
  have hFU : ∀ f ∈ F, f ∈ Subgroup.normalizer (U : Set G) := fun f hf =>
    mem_normalizer_commutator (hFV hf) (hFL f hf)
  have hUV : U ≤ V := commutator_le_left_of_le_normalizer (hLF.trans hFV)
  have hVU : V ≤ U ⊔ ⁅V, P⁆ := by
    refine h.trans (Subgroup.commutator_le.mpr fun v hv f hf => ?_)
    have hf' : f ∈ ((P ⊔ L : Subgroup G) : Set G) := by
      rw [sup_comm]; exact hFLP hf
    rw [Subgroup.coe_mul_of_left_le_normalizer_right P L
      (fun p hp => hFL p (hPF hp))] at hf'
    obtain ⟨p, hp, l, hl, rfl⟩ := hf'
    have e : ⁅v, p * l⁆ = ⁅v, p⁆ * (p * ⁅v, l⁆ * p⁻¹) := by
      simp [commutatorElement_def]
      group
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hv hp))
      (Subgroup.mem_sup_left ?_)
    exact (Subgroup.mem_normalizer_iff.mp (hFU p (hPF hp)) _).mp
      (Subgroup.commutator_mem_commutator hv hl)
  set K : Subgroup G := V ⊔ P with hKdef
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := hPF.trans hFV
  have hV2g : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hV2 x x.2)⟩
  have hK : IsPGroup 2 K := hV2g.to_sup_of_normal_left' hP.2.1 hPV
  have : Group.IsNilpotent K := hK.isNilpotent
  have hVN : V ≤ Subgroup.normalizer (U : Set G) := fun v hv =>
    Subgroup.centralizer_le_normalizer (U : Set G) (Subgroup.mem_centralizer_iff.mpr
      fun x hx => (hV v hv x (hUV hx)).symm)
  have hKN : K ≤ Subgroup.normalizer (U : Set G) :=
    sup_le hVN fun p hp => hFU p (hPF hp)
  have : (U.subgroupOf K).Normal := ⟨fun n hn g => by
    have hg := (Subgroup.mem_normalizer_iff.mp (hKN g.2) n).mp hn
    simpa [Subgroup.mem_subgroupOf] using hg⟩
  have hVK : V ≤ K := le_sup_left
  have hUK : U ≤ K := hUV.trans hVK
  have hmain : V.subgroupOf K ≤ U.subgroupOf K := by
    refine le_of_le_sup_commutator_top _ _ ?_
    rw [← Subgroup.map_le_map_iff_of_injective K.subtype_injective, Subgroup.map_sup,
      Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.map_top, Subgroup.range_subtype, inf_of_le_left hVK, inf_of_le_left hUK]
    exact hVU.trans (sup_le_sup_left (Subgroup.commutator_mono le_rfl le_sup_right) _)
  intro v hv
  have := hmain (show (⟨v, hVK hv⟩ : K) ∈ V.subgroupOf K from hv)
  exact this
