module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K108BigCell
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem
open scoped Pointwise

variable {G : Type} [Group G] {B N : Subgroup G} [(cartan B N).Normal]
  {S : Set (WeylGroup B N)}

theorem k108big_exists_conj_fixed [Finite G] (h : IsBNPair B N S) {p q : ℕ} [hp : Fact p.Prime]
    [hq : Fact q.Prime] (hpq : p ≠ q) {U : Subgroup G} (hUp : IsPGroup p U) (hUleB : U ≤ B)
    (hUB : B ≤ Subgroup.normalizer (U : Set G)) (hBU : B ≤ U ⊔ (B ⊓ N))
    {w₀ : WeylGroup B N} (hmax : ∀ w, wordLength S w ≤ wordLength S w₀)
    {Q : Type*} [Group Q] (hQ : IsPGroup q Q) (φ : Q →* MulAut G)
    (hφB : ∀ a x, φ a x ∈ B ↔ x ∈ B) (hφU : ∀ a, U.map (φ a).toMonoidHom = U) :
    ∃ g ∈ dc B N w₀, ∀ a, (U.map (MulAut.conj g).toMonoidHom).map (φ a).toMonoidHom =
      U.map (MulAut.conj g).toMonoidHom := by
  classical
  have hconj : ∀ (K : Subgroup G) (a b : G), K.map (MulAut.conj (b * a)).toMonoidHom =
      (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom := fun K a b => by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  have hconjφ : ∀ (K : Subgroup G) (f : G ≃* G) (g : G),
      (K.map (MulAut.conj g).toMonoidHom).map f.toMonoidHom =
        (K.map f.toMonoidHom).map (MulAut.conj (f g)).toMonoidHom := fun K f g => by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [map_mul, map_inv]
  obtain ⟨n₀, hn₀⟩ := QuotientGroup.mk_surjective w₀
  have hn₀mem : (n₀ : G) ∈ dc B N w₀ := hn₀ ▸ coe_mem_dc n₀
  set V₀ := U.map (MulAut.conj (n₀ : G)).toMonoidHom with hV₀
  have hfix : ∀ c ∈ B, U.map (MulAut.conj c).toMonoidHom = U := fun c hc =>
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hUB hc)
  have hHV₀ := k108big_cartan_le_normalizer_conj hUB n₀
  letI actU : MulAction U (Subgroup G) := MulAction.compHom _ (MulAut.conj.comp U.subtype)
  have smulU : ∀ (u : U) (V : Subgroup G), u • V = V.map (MulAut.conj (u : G)).toMonoidHom :=
    fun _ _ => rfl
  have hmemΩ : ∀ g ∈ dc B N w₀, U.map (MulAut.conj g).toMonoidHom ∈ MulAction.orbit U V₀ := by
    intro g hg
    obtain ⟨b, hb, b', hb', rfl⟩ := (mem_dc_of_lift hn₀).1 hg
    have hb2 : b ∈ ((U ⊔ (B ⊓ N) : Subgroup G) : Set G) := hBU hb
    rw [Subgroup.coe_mul_of_right_le_normalizer_left U (B ⊓ N) (inf_le_left.trans hUB)] at hb2
    obtain ⟨u, hu, c, hc, rfl⟩ := hb2
    refine ⟨⟨u, hu⟩, ?_⟩
    dsimp only
    rw [smulU]
    have hcV : V₀.map (MulAut.conj c).toMonoidHom = V₀ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hHV₀ hc)
    rw [hconj U b' (u * c * (n₀ : G)), hfix b' hb', hconj U (n₀ : G) (u * c), ← hV₀,
      hconj V₀ c u, hcV]
  letI actQ : MulAction Q (Subgroup G) := MulAction.compHom _ φ
  have smulQ : ∀ (a : Q) (V : Subgroup G), a • V = V.map (φ a).toMonoidHom := fun _ _ => rfl
  let Ω : SubMulAction Q (Subgroup G) :=
    { carrier := MulAction.orbit U V₀
      smul_mem' := fun a V hV => by
        obtain ⟨u, rfl⟩ := hV
        dsimp only
        rw [smulQ, smulU]
        have hg : (u : G) * (n₀ : G) ∈ dc B N w₀ := by
          simpa using mul_mem_dc hn₀mem (hUleB u.2) B.one_mem
        have e : (V₀.map (MulAut.conj (u : G)).toMonoidHom).map (φ a).toMonoidHom =
            U.map (MulAut.conj ((φ a) ((u : G) * (n₀ : G)))).toMonoidHom := by
          rw [hV₀, ← hconj U (n₀ : G) (u : G), hconjφ, hφU]
        rw [e]
        apply hmemΩ
        rw [← k108big_image_dc_longest h (φ a) (hφB a) hmax]
        exact ⟨_, hg, rfl⟩ }
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective
  obtain ⟨k, hk⟩ := hUp.card_orbit V₀
  have hcard : ¬ q ∣ Nat.card Ω := by
    change ¬ q ∣ Nat.card (MulAction.orbit U V₀)
    rw [hk]
    intro hdvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).1 (hq.out.dvd_of_dvd_pow hdvd)).symm
  obtain ⟨⟨V, hV⟩, hfixV⟩ := hQ.nonempty_fixed_point_of_prime_not_dvd_card Ω hcard
  obtain ⟨u, rfl⟩ := hV
  refine ⟨(u : G) * (n₀ : G), ?_, fun a => ?_⟩
  · simpa using mul_mem_dc hn₀mem (hUleB u.2) B.one_mem
  · have hfa := congrArg Subtype.val (hfixV a)
    have e : U.map (MulAut.conj ((u : G) * (n₀ : G))).toMonoidHom = u • V₀ := by
      rw [smulU, hV₀, hconj]
    rw [e]
    exact hfa

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
