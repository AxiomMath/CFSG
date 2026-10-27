module

public import CFSG.Quasithin.Background.C116Three.ModuleDefs

import CFSG.Quasithin.H13.NQRigidWMGroups
import CFSG.Quasithin.EmptyFaithful.S146zXGIdent
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.EmptyFaithful.R3c23PairAFac
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V] [Finite V]

private theorem case3_hom_trivial_of_perfect {N A : Type} [Group N] [CommGroup A]
    [Group.IsPerfect N] (f : N →* A) (x : N) : f x = 1 := by
  have hc : ⁅(⊤ : Subgroup N), (⊤ : Subgroup N)⁆ ≤ f.ker := by
    rw [Subgroup.commutator_le]
    intro g _ h _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hx : x ∈ ⁅(⊤ : Subgroup N), (⊤ : Subgroup N)⁆ := Group.IsPerfect.mem_commutator
  exact MonoidHom.mem_ker.mp (hc hx)

private theorem case3_perm5_perfect_le_alt (N : Subgroup (Equiv.Perm (Fin 5)))
    [Group.IsPerfect N] : N ≤ alternatingGroup (Fin 5) := by
  intro x hx
  have h := case3_hom_trivial_of_perfect ((Equiv.Perm.sign).comp N.subtype) ⟨x, hx⟩
  rw [Equiv.Perm.mem_alternatingGroup]
  simpa using h

private theorem case3_perm5_perfect_normal_eq (N : Subgroup (Equiv.Perm (Fin 5)))
    [N.Normal] [Group.IsPerfect N] (hN : N ≠ ⊥) : N = alternatingGroup (Fin 5) := by
  have hle := case3_perm5_perfect_le_alt N
  rcases Subgroup.Normal.eq_bot_or_eq_top (N.subgroupOf (alternatingGroup (Fin 5))) with h | h
  · exfalso
    apply hN
    have h' := congrArg (Subgroup.map (alternatingGroup (Fin 5)).subtype) h
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_bot, inf_eq_left.mpr hle] at h'
    exact h'
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp h)

private theorem case3_normal_of_jn {X L : Subgroup (MulAut V)}
    (hJn : ∀ x ∈ ffJ X, x ∈ Subgroup.normalizer (L : Set (MulAut V))) :
    ∀ x ∈ ffJ X, ∀ k ∈ L, x * k * x⁻¹ ∈ L :=
  fun x hx k hk => (Subgroup.mem_normalizer_iff.mp (hJn x hx) k).mp hk

private theorem case3_ne_bot_of_qs {K : Subgroup (MulAut V)} (hK : CFSG.IsQuasisimple ↥K) :
    K ≠ ⊥ := by
  intro h
  refine CFSG.Quasithin.InternalSec.not_commute_of_isQuasisimple hK (fun a ha b hb => ?_)
  rw [h, Subgroup.mem_bot] at ha hb
  rw [ha, hb]

private theorem case3_isPerfect {L : Subgroup (MulAut V)} (hq : CFSG.IsQuasisimple ↥L) :
    Group.IsPerfect ↥L :=
  hq.1

private theorem case3_not_solvable {L : Subgroup (MulAut V)} (hq : CFSG.IsQuasisimple ↥L) :
    ¬ Group.IsSolvable ↥L := by
  haveI : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr (case3_ne_bot_of_qs hq)
  haveI : Group.IsPerfect ↥L := case3_isPerfect hq
  exact Group.IsPerfect.not_isSolvable ↥L

private theorem case3_false_of_card_six {G L : Subgroup (MulAut V)} (hG : Nat.card ↥G = 6)
    (hLG : L ≤ G) (hq : CFSG.IsQuasisimple ↥L) : False := by
  haveI : Group.IsSolvable ↥G := twoG_isSolvable_of_card_six hG
  have : Group.IsSolvable ↥L :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLG)
      (Subgroup.inclusion_injective hLG)
  exact case3_not_solvable hq this

private theorem case3_subgroupOf_normal {G L : Subgroup (MulAut V)}
    (hn : ∀ x ∈ G, ∀ k ∈ L, x * k * x⁻¹ ∈ L) : (L.subgroupOf G).Normal :=
  ⟨fun n hn' g => by
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    simpa using hn g.1 g.2 n.1 hn'⟩

private theorem case3_simple_eq {G L : Subgroup (MulAut V)} (hG : IsSimpleGroup ↥G)
    (hLG : L ≤ G) (hn : ∀ x ∈ G, ∀ k ∈ L, x * k * x⁻¹ ∈ L) (hL : L ≠ ⊥) : G = L := by
  haveI := case3_subgroupOf_normal hn
  rcases Subgroup.Normal.eq_bot_or_eq_top (L.subgroupOf G) with h | h
  · exfalso
    apply hL
    have h' := congrArg (Subgroup.map G.subtype) h
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_bot, inf_eq_left.mpr hLG] at h'
    exact h'
  · exact le_antisymm (Subgroup.subgroupOf_eq_top.mp h) hLG

private theorem case3_perm5_map {G L : Subgroup (MulAut V)} (e : ↥G ≃* Equiv.Perm (Fin 5))
    (hLG : L ≤ G) (hn : ∀ x ∈ G, ∀ k ∈ L, x * k * x⁻¹ ∈ L) (hq : CFSG.IsQuasisimple ↥L) :
    (L.subgroupOf G).map e.toMonoidHom = alternatingGroup (Fin 5) := by
  haveI : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr (case3_ne_bot_of_qs hq)
  haveI : Group.IsPerfect ↥L := case3_isPerfect hq
  haveI hNn := case3_subgroupOf_normal hn
  let eLM : ↥L ≃* ↥((L.subgroupOf G).map e.toMonoidHom) :=
    (Subgroup.subgroupOfEquivOfLe hLG).symm.trans (MulEquiv.subgroupMap e (L.subgroupOf G))
  haveI : Group.IsPerfect ↥((L.subgroupOf G).map e.toMonoidHom) :=
    Group.IsPerfect.ofSurjective (f := eLM.toMonoidHom) eLM.surjective
  haveI : ((L.subgroupOf G).map e.toMonoidHom).Normal :=
    Subgroup.Normal.map hNn e.toMonoidHom e.surjective
  have hne : (L.subgroupOf G).map e.toMonoidHom ≠ ⊥ := by
    haveI : Nontrivial ↥((L.subgroupOf G).map e.toMonoidHom) := eLM.toEquiv.symm.nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance
  exact case3_perm5_perfect_normal_eq _ hne

private theorem case3_perm5_card {G L : Subgroup (MulAut V)} (e : ↥G ≃* Equiv.Perm (Fin 5))
    (hLG : L ≤ G) (hn : ∀ x ∈ G, ∀ k ∈ L, x * k * x⁻¹ ∈ L) (hq : CFSG.IsQuasisimple ↥L) :
    Nat.card ↥L = 60 := by
  have hmap := case3_perm5_map e hLG hn hq
  have hcard : Nat.card ↥L = Nat.card ↥((L.subgroupOf G).map e.toMonoidHom) :=
    Nat.card_congr ((Subgroup.subgroupOfEquivOfLe hLG).symm.trans
      (MulEquiv.subgroupMap e (L.subgroupOf G))).toEquiv
  rw [hcard, hmap, nat_card_alternatingGroup]
  simp [Nat.factorial]

private theorem case3_sl2_one_card {G : Subgroup (MulAut V)} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 1) (e : ↥G ≃* ↥(StatedSL 2 K)) : Nat.card ↥G = 6 := by
  rw [Nat.card_congr e.toEquiv, twoG_card_statedSL_two, hK]
  norm_num

private theorem case3_sl2_simple {G : Subgroup (MulAut V)} {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (e : ↥G ≃* ↥(StatedSL 2 K)) :
    IsSimpleGroup ↥G := by
  haveI := twoG_charP_two hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI := CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
  exact e.isSimpleGroup

private theorem case3_sl3_simple {G : Subgroup (MulAut V)} {K : Type} [Field K] [Finite K]
    {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm : Odd m) (e : ↥G ≃* ↥(StatedSL 3 K)) :
    IsSimpleGroup ↥G := by
  haveI := CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_three_odd hK hm
  exact e.isSimpleGroup

private theorem case3_factor_kind {G : Subgroup (MulAut V)} (hF : B56FactorList ↥G) :
    Nat.card ↥G = 6 ∨ IsSimpleGroup ↥G ∨ Nonempty (↥G ≃* Equiv.Perm (Fin 5)) := by
  rcases hF with ⟨n, K, _, _, hn, hK, ⟨e⟩⟩ | e | ⟨m, K, _, _, hm, hodd, hK, ⟨e⟩⟩
  · rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 1 := by omega
      exact Or.inl (case3_sl2_one_card hK e)
    · exact Or.inr (Or.inl (case3_sl2_simple h2 hK e))
  · exact Or.inr (Or.inr e)
  · exact Or.inr (Or.inl (case3_sl3_simple hK hodd e))

private theorem case3_lin2Cover_of_alt5 {L : Type} [Group L]
    (e : L ≃* ↥(alternatingGroup (Fin 5))) : Lin2Cover L := by
  obtain ⟨f⟩ := CFSG.Quasithin.S146zX.nonempty_mulEquiv_sl_two_four_of_alt_five
  exact ⟨GaloisField 2 2, inferInstance, inferInstance, 2, le_refl 2,
    GaloisField.card 2 2 (by norm_num),
    ⟨(e.trans f.symm).trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (GaloisField 2 2))⟩⟩

private theorem case3_lin2Cover_of_sl2 {L : Type} [Group L] {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (e : L ≃* ↥(StatedSL 2 K)) :
    Lin2Cover L :=
  ⟨K, inferInstance, inferInstance, n, hn, hK, ⟨e⟩⟩

private theorem case3_perm5_iso {G L : Subgroup (MulAut V)} (e : ↥G ≃* Equiv.Perm (Fin 5))
    (hLG : L ≤ G) (hn : ∀ x ∈ G, ∀ k ∈ L, x * k * x⁻¹ ∈ L) (hq : CFSG.IsQuasisimple ↥L) :
    Nonempty (↥L ≃* ↥(alternatingGroup (Fin 5))) :=
  ⟨(Subgroup.subgroupOfEquivOfLe hLG).symm.trans ((MulEquiv.subgroupMap e (L.subgroupOf G)).trans
    (MulEquiv.subgroupCongr (case3_perm5_map e hLG hn hq)))⟩

private theorem case3_core {G L : Subgroup (MulAut V)} (hF : B56FactorList ↥G) (hLG : L ≤ G)
    (hn : ∀ x ∈ G, ∀ k ∈ L, x * k * x⁻¹ ∈ L) (hq : CFSG.IsQuasisimple ↥L) :
    (G = L ∨ (Nonempty (↥G ≃* Equiv.Perm (Fin 5)) ∧ Nat.card ↥L = 60)) ∧
      (Lin2Cover ↥L ∨ ∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 1 ≤ m ∧ Odd m ∧
        Nat.card K = 2 ^ m ∧ Nonempty (↥L ≃* ↥(StatedSL 3 K))) := by
  rcases hF with ⟨n, K, _, _, hn1, hK, ⟨e⟩⟩ | e | ⟨m, K, _, _, hm, hodd, hK, ⟨e⟩⟩
  · rcases Nat.lt_or_ge n 2 with h2 | h2
    · exfalso
      obtain rfl : n = 1 := by omega
      exact case3_false_of_card_six (case3_sl2_one_card hK e) hLG hq
    · have heq : G = L :=
        case3_simple_eq (case3_sl2_simple h2 hK e) hLG hn (case3_ne_bot_of_qs hq)
      exact ⟨Or.inl heq,
        Or.inl (case3_lin2Cover_of_sl2 h2 hK ((MulEquiv.subgroupCongr heq).symm.trans e))⟩
  · obtain ⟨e'⟩ := e
    obtain ⟨eL⟩ := case3_perm5_iso e' hLG hn hq
    exact ⟨Or.inr ⟨⟨e'⟩, case3_perm5_card e' hLG hn hq⟩,
      Or.inl (case3_lin2Cover_of_alt5 eL)⟩
  · have heq : G = L :=
      case3_simple_eq (case3_sl3_simple hK hodd e) hLG hn (case3_ne_bot_of_qs hq)
    exact ⟨Or.inl heq, Or.inr ⟨m, K, inferInstance, inferInstance, hm, hodd, hK,
      ⟨(MulEquiv.subgroupCongr heq).symm.trans e⟩⟩⟩

private theorem case3_eq_of_subgroupOf_eq {G L₁ L₂ : Subgroup (MulAut V)} (hL₁ : L₁ ≤ G)
    (hL₂ : L₂ ≤ G) (h : L₁.subgroupOf G = L₂.subgroupOf G) : L₁ = L₂ := by
  have e1 : L₁ = (L₁.subgroupOf G).map G.subtype := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hL₁]
  have e2 : L₂ = (L₂.subgroupOf G).map G.subtype := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hL₂]
  calc L₁ = (L₁.subgroupOf G).map G.subtype := e1
    _ = (L₂.subgroupOf G).map G.subtype := by rw [h]
    _ = L₂ := e2.symm

private theorem case3_same_eq {G L₁ L₂ : Subgroup (MulAut V)} (hF : B56FactorList ↥G)
    (hL₁ : L₁ ≤ G) (hL₂ : L₂ ≤ G) (hn₁ : ∀ x ∈ G, ∀ k ∈ L₁, x * k * x⁻¹ ∈ L₁)
    (hn₂ : ∀ x ∈ G, ∀ k ∈ L₂, x * k * x⁻¹ ∈ L₂) (hq₁ : CFSG.IsQuasisimple ↥L₁)
    (hq₂ : CFSG.IsQuasisimple ↥L₂) : L₁ = L₂ := by
  rcases case3_factor_kind hF with h6 | hS | e
  · exact (case3_false_of_card_six h6 hL₁ hq₁).elim
  · exact (case3_simple_eq hS hL₁ hn₁ (case3_ne_bot_of_qs hq₁)).symm.trans
      (case3_simple_eq hS hL₂ hn₂ (case3_ne_bot_of_qs hq₂))
  · obtain ⟨e⟩ := e
    have hmap : (L₁.subgroupOf G).map e.toMonoidHom = (L₂.subgroupOf G).map e.toMonoidHom :=
      (case3_perm5_map e hL₁ hn₁ hq₁).trans (case3_perm5_map e hL₂ hn₂ hq₂).symm
    have hinj : Function.Injective e.toMonoidHom := fun a b hab => e.injective hab
    exact case3_eq_of_subgroupOf_eq hL₁ hL₂ (Subgroup.map_injective hinj hmap)

private theorem case3_false_of_eq {L₁ L₂ : Subgroup (MulAut V)} (hq : CFSG.IsQuasisimple ↥L₁)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (h : L₁ = L₂) : False := by
  subst h
  exact CFSG.Quasithin.InternalSec.not_commute_of_isQuasisimple hq hcomm

private theorem case3_conj_part {X L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V}
    (hconj : L₂ = L₁.map (MulAut.conj τ).toMonoidHom)
    (hτN : τ ∈ Subgroup.normalizer (ffJ X : Set (MulAut V)))
    (hL₁J : L₁ ≤ ffJ X) (hn₁ : ∀ x ∈ ffJ X, ∀ k ∈ L₁, x * k * x⁻¹ ∈ L₁) :
    L₂ ≤ ffJ X ∧ ∀ x ∈ ffJ X, ∀ k ∈ L₂, x * k * x⁻¹ ∈ L₂ := by
  have hfw : ∀ g ∈ ffJ X, τ * g * τ⁻¹ ∈ ffJ X := fun g hg =>
    (Subgroup.mem_normalizer_iff.mp hτN g).mp hg
  have hbk : ∀ g ∈ ffJ X, τ⁻¹ * g * τ ∈ ffJ X := fun g hg => by
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hτN) g).mp hg
    rwa [inv_inv] at h
  have hmem : ∀ k ∈ L₂, ∃ a ∈ L₁, τ * a * τ⁻¹ = k := by
    intro k hk
    rw [hconj, Subgroup.mem_map] at hk
    obtain ⟨a, ha, hak⟩ := hk
    exact ⟨a, ha, hak⟩
  refine ⟨?_, ?_⟩
  · intro k hk
    obtain ⟨a, ha, rfl⟩ := hmem k hk
    exact hfw a (hL₁J ha)
  · intro x hx k hk
    obtain ⟨a, ha, rfl⟩ := hmem k hk
    have hy : τ⁻¹ * x * τ * a * (τ⁻¹ * x * τ)⁻¹ ∈ L₁ := hn₁ (τ⁻¹ * x * τ) (hbk x hx) a ha
    have e : x * (τ * a * τ⁻¹) * x⁻¹ = τ * (τ⁻¹ * x * τ * a * (τ⁻¹ * x * τ)⁻¹) * τ⁻¹ := by
      group
    rw [e, hconj]
    exact Subgroup.mem_map_of_mem (MulAut.conj τ).toMonoidHom hy

private theorem case3_good {X L₁ L₂ G₁ G₂ : Subgroup (MulAut V)} {W₁ W₂ : Subgroup V}
    (hsup : G₁ ⊔ G₂ = ffJ X) (hdisj : G₁ ⊓ G₂ = ⊥) (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (hL₁ : L₁ ≤ G₁) (hL₂ : L₂ ≤ G₂) (hF₁ : B56FactorList ↥G₁) (hF₂ : B56FactorList ↥G₂)
    (hq₁ : CFSG.IsQuasisimple ↥L₁) (hq₂ : CFSG.IsQuasisimple ↥L₂)
    (hn₁ : ∀ x ∈ ffJ X, ∀ k ∈ L₁, x * k * x⁻¹ ∈ L₁)
    (hn₂ : ∀ x ∈ ffJ X, ∀ k ∈ L₂, x * k * x⁻¹ ∈ L₂)
    (hfix₁ : fixV (ffJ X) ≤ W₁) (hfix₂ : fixV (ffJ X) ≤ W₂)
    (hinv₁ : XMod.IsInv ↥(ffJ X) W₁) (hinv₂ : XMod.IsInv ↥(ffJ X) W₂)
    (hW : W₁ ⊔ W₂ = ⊤) (hWI : W₁ ⊓ W₂ = fixV (ffJ X))
    (hP₁ : B56Piece G₁ W₁ (fixV (ffJ X))) (hP₂ : B56Piece G₂ W₂ (fixV (ffJ X))) :
    TypeTwo X L₁ L₂ ∨ TypeThree X L₁ L₂ := by
  have hG₁J : G₁ ≤ ffJ X := by rw [← hsup]; exact le_sup_left
  have hG₂J : G₂ ≤ ffJ X := by rw [← hsup]; exact le_sup_right
  obtain ⟨hc₁, hl₁⟩ := case3_core hF₁ hL₁ (fun x hx => hn₁ x (hG₁J hx)) hq₁
  obtain ⟨hc₂, -⟩ := case3_core hF₂ hL₂ (fun x hx => hn₂ x (hG₂J hx)) hq₂
  have hgen : TwoB56Gen X L₁ L₂ :=
    ⟨G₁, G₂, W₁, W₂, hsup.symm, hdisj, hcomm, hL₁, hL₂, hc₁, hc₂,
      (by rw [hsup]; exact hfix₁), (by rw [hsup]; exact hfix₂), hW,
      (by rw [hsup]; exact hWI), (by rw [hsup]; exact hP₁), (by rw [hsup]; exact hP₂)⟩
  have hinv : TwoB56GenInv X L₁ L₂ :=
    ⟨G₁, G₂, W₁, W₂, hsup.symm, hdisj, hcomm, hL₁, hL₂, hc₁, hc₂,
      (by rw [hsup]; exact hfix₁), (by rw [hsup]; exact hfix₂), hW,
      (by rw [hsup]; exact hWI), (by rw [hsup]; exact hP₁), (by rw [hsup]; exact hP₂),
      (by rw [hsup]; exact hinv₁), (by rw [hsup]; exact hinv₂)⟩
  rcases hl₁ with hl | hl3
  · exact Or.inl ⟨hgen, hl⟩
  · exact Or.inr ⟨hinv, hl3⟩

theorem case3_shape (hV : ∀ v : V, v ^ 2 = 1) {X L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V}
    (P : JPair X L₁ L₂ τ) (h3 : B56Case3 (ffJ X)) : TypeTwo X L₁ L₂ ∨ TypeThree X L₁ L₂ := by
  obtain ⟨A₁, A₂, hsupA, hdisjA, hcommA, hFA₁, hFA₂, W₁, W₂, hfix₁, hfix₂, hinv₁, hinv₂,
    hW, hWI, hP₁, hP₂⟩ := h3
  have hτN : τ ∈ Subgroup.normalizer (ffJ X : Set (MulAut V)) :=
    CFSG.Quasithin.B6.le_normalizer_ffJ X P.τ_mem
  have hn₁ : ∀ x ∈ ffJ X, ∀ k ∈ L₁, x * k * x⁻¹ ∈ L₁ := case3_normal_of_jn P.Jn
  obtain ⟨hL₂J, hn₂⟩ := case3_conj_part P.conj hτN P.L₁J hn₁
  have hA₁J : A₁ ≤ ffJ X := by rw [← hsupA]; exact le_sup_left
  have hA₂J : A₂ ≤ ffJ X := by rw [← hsupA]; exact le_sup_right
  have hLa : L₁ ≤ A₁ ∨ L₁ ≤ A₂ :=
    CFSG.Quasithin.InternalSec.le_or_le_of_sup_eq hsupA hcommA P.L₁J hn₁ P.q₁
  have hLb : L₂ ≤ A₁ ∨ L₂ ≤ A₂ :=
    CFSG.Quasithin.InternalSec.le_or_le_of_sup_eq hsupA hcommA hL₂J hn₂ P.q₂
  rcases hLa with hLa | hLa <;> rcases hLb with hLb | hLb
  ·
    exact (case3_false_of_eq P.q₁ P.comm (case3_same_eq hFA₁ hLa hLb
      (fun x hx => hn₁ x (hA₁J hx)) (fun x hx => hn₂ x (hA₁J hx)) P.q₁ P.q₂)).elim
  ·
    exact case3_good hsupA hdisjA hcommA hLa hLb hFA₁ hFA₂ P.q₁ P.q₂ hn₁ hn₂
      hfix₁ hfix₂ hinv₁ hinv₂ hW hWI hP₁ hP₂
  ·
    exact case3_good (G₁ := A₂) (G₂ := A₁) (W₁ := W₂) (W₂ := W₁)
      (by rw [sup_comm]; exact hsupA) (by rw [inf_comm]; exact hdisjA)
      (fun a ha b hb => (hcommA b hb a ha).symm) hLa hLb hFA₂ hFA₁ P.q₁ P.q₂ hn₁ hn₂
      hfix₂ hfix₁ hinv₂ hinv₁ (by rw [sup_comm]; exact hW) (by rw [inf_comm]; exact hWI)
      hP₂ hP₁
  ·
    exact (case3_false_of_eq P.q₁ P.comm (case3_same_eq hFA₂ hLa hLb
      (fun x hx => hn₁ x (hA₂J hx)) (fun x hx => hn₂ x (hA₂J hx)) P.q₁ P.q₂)).elim

end CFSG.Quasithin.C116Three
