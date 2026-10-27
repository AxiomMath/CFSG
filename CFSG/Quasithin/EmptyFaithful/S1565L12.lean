module

public import CFSG.Quasithin.EmptyFaithful.S1565L3
public import CFSG.Quasithin.Background.F918P6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1565

section StarIso

variable {G : Type} [Group G]

private noncomputable def starMapL12 (M' H K : Subgroup G) (hKH : K ≤ H) :
    ↥K →* ↥(E2.star M' H K) :=
  (((QuotientGroup.mk' ((kerIn M' H).subgroupOf H)).comp (Subgroup.inclusion hKH)).codRestrict
    (E2.star M' H K) fun k => ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩)

private theorem starMapL12_surjective (M' H K : Subgroup G) (hKH : K ≤ H) :
    Function.Surjective (starMapL12 M' H K hKH) := by
  rintro ⟨y, x, hx, rfl⟩
  refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
  apply Subtype.ext
  rfl

private theorem starMapL12_eq_one_iff (M' H K : Subgroup G) (hKH : K ≤ H) (k : ↥K) :
    starMapL12 M' H K hKH k = 1 ↔ Subgroup.inclusion hKH k ∈ (kerIn M' H).subgroupOf H := by
  constructor
  · intro h
    have := congrArg Subtype.val h
    exact (QuotientGroup.eq_one_iff _).mp this
  · intro h
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr h

theorem nonempty_mulEquiv_star_of_surjective {M' H K : Subgroup G} (hKH : K ≤ H) {L : Type} [Group L]
    [Nontrivial L] (ρ : ↥K →* L) (hρ : Function.Surjective ρ)
    (hker : ∀ k : ↥K, Subgroup.inclusion hKH k ∈ (kerIn M' H).subgroupOf H → ρ k = 1)
    (hsimple : IsSimpleGroup ↥(E2.star M' H K)) : Nonempty (↥(E2.star M' H K) ≃* L) := by
  have hq := starMapL12_surjective M' H K hKH
  have hkq : (starMapL12 M' H K hKH).ker ≤ ρ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker, starMapL12_eq_one_iff] at hk
    exact hker k hk
  let ρ' : ↥(E2.star M' H K) →* L :=
    (starMapL12 M' H K hKH).liftOfRightInverse (Function.surjInv hq)
      (Function.rightInverse_surjInv hq) ⟨ρ, hkq⟩
  have hρ'q : ∀ k, ρ' (starMapL12 M' H K hKH k) = ρ k := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨ρ, hkq⟩ k
  have hρ's : Function.Surjective ρ' := by
    intro l
    obtain ⟨k, rfl⟩ := hρ l
    exact ⟨starMapL12 M' H K hKH k, hρ'q k⟩
  have hρ'i : Function.Injective ρ' := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hsimple.eq_bot_or_eq_top_of_normal ρ'.ker with h | h
    · exact h
    · exfalso
      obtain ⟨l₁, hl₁⟩ := exists_ne (1 : L)
      obtain ⟨y, rfl⟩ := hρ's l₁
      have : y ∈ ρ'.ker := by rw [h]; trivial
      exact hl₁ (by simpa using this)
  exact ⟨MulEquiv.ofBijective ρ' ⟨hρ'i, hρ's⟩⟩

end StarIso

section Transfer

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

omit [Finite G] in
private theorem inclEU_actH_pow (hF : HypF918 T V L V₁ Vp H K) {I : Subgroup G}
    (hIU : I ≤ conjClosure Vp H) [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H)))] (x : ↥H) (n : ℕ)
    (e : ↥(tildeOf V₁ (conjClosure I H))) :
    ((actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) x) ^ n) (inclEU V₁ hIU e) =
      inclEU V₁ hIU (((actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x) ^ n) e) := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ]
    show (actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) x ^ n)
        (actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) x (inclEU V₁ hIU e)) =
      inclEU V₁ hIU ((actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x ^ n)
        (actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x e))
    rw [← inclEU_actH hF hIU x e]
    exact ih _

theorem chiefFreeBelow15365_of_good_tilde (hF : HypF918 T V L V₁ Vp H K) (hHK : H = K ⊔ T)
    {I : Subgroup G} [hFU : Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H)))]
    [hFI : Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] (M : Subgroup G)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (t₀ : ↥H) (ht₀ : (t₀ : G) ∈ M) {m : ℕ}
    (hodd : Odd m)
    (hfm : (actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) t₀) ^ m = 1)
    (hgood : ∀ w : ↥(tildeOf V₁ (conjClosure I H)),
      actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) t₀ w * w⁻¹ ∈
        fixV (autIH V₁ I H (conjClosure K T)) → w ∈ fixV (autIH V₁ I H (conjClosure K T))) :
    ChiefFreeBelow15365 hF M I := by
  have hKT : conjClosure K T ≤ H := hF.K₀_le_H
  refine chiefFreeBelow15365_of_odd_element hF hHK M I hV₁I hIU t₀ ht₀ hodd ?_ ?_
  · intro w hw
    have hw' : (w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) ∈
        tildeOf V₁ (conjClosure I H) := mem_subM_iff.mp hw
    have hwe : w = inclEU V₁ hIU ⟨(w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁), hw'⟩ :=
      Subtype.ext rfl
    rw [hwe, inclEU_actH_pow hF hIU t₀ m, hfm]
    rfl
  · intro w hw hC
    have hw' : (w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) ∈
        tildeOf V₁ (conjClosure I H) := mem_subM_iff.mp hw
    set e : ↥(tildeOf V₁ (conjClosure I H)) :=
      ⟨(w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁), hw'⟩ with he
    have hwe : w = inclEU V₁ hIU e := Subtype.ext rfl
    have hinj := inclEU_injective (V₁ := V₁) hIU
    have hactw : actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) t₀ w * w⁻¹ =
        inclEU V₁ hIU
          (actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) t₀ e * e⁻¹) := by
      rw [hwe, ← inclEU_actH hF hIU t₀ e, map_mul, map_inv]
    have hCe : actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) t₀ e * e⁻¹ ∈
        fixV (autIH V₁ I H (conjClosure K T)) := by
      intro g hg
      rw [autIH_eq_map hF hKT] at hg
      obtain ⟨s, hs, rfl⟩ := hg
      have h1 := hC s hs
      rw [Subgroup.mem_bot, hactw, ← inclEU_actH hF hIU s, ← map_inv, ← map_mul,
        map_eq_one_iff _ hinj, mul_inv_eq_one] at h1
      exact h1
    have he' := hgood e hCe
    intro s hs
    rw [Subgroup.mem_bot, hwe, ← inclEU_actH hF hIU s, ← map_inv, ← map_mul, map_eq_one_iff _ hinj]
    have hmem : actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) s ∈
        autIH V₁ I H (conjClosure K T) := by
      rw [autIH_eq_map hF hKT]
      exact ⟨s, hs, rfl⟩
    have := he' _ hmem
    exact mul_inv_eq_one.mpr this

end Transfer

end CFSG.Quasithin
