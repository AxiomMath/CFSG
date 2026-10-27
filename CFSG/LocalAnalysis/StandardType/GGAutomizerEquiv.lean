module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.Mathlib.GroupTheory.Automorphism.ConjCommute
import CFSG.GH74.E2.Cl2Rank

public section

namespace CFSG.StandardType

theorem ggAutomizer_top_map_equiv {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (A : Subgroup G) :
    ggAutomizer (⊤ : Subgroup H) (A.map e.toMonoidHom) =
      (ggAutomizer (⊤ : Subgroup G) A).map
        (MulAut.congr (A.equivMapOfInjective e.toMonoidHom e.injective)).toMonoidHom := by
  classical
  let E := A.map e.toMonoidHom
  let θ : A ≃* E := A.equivMapOfInjective e.toMonoidHom e.injective
  have hθ : ∀ a : A, (θ a : H) = e (a : G) := fun _ => rfl
  have hmem : ∀ g : G, e g ∈ E ↔ g ∈ A := by
    intro g
    constructor
    · rintro ⟨a, ha, hag⟩
      exact e.injective hag ▸ ha
    · intro hg
      exact Subgroup.mem_map_of_mem e.toMonoidHom hg
  have hnorm : ∀ g : G, e g ∈ Subgroup.normalizer (E : Set H) ↔
      g ∈ Subgroup.normalizer (A : Set G) := by
    intro g
    constructor
    · intro hg
      rw [Subgroup.mem_normalizer_iff]
      intro a
      have h := Subgroup.mem_normalizer_iff.mp hg (e a)
      rw [← map_inv, ← map_mul, ← map_mul, hmem, hmem] at h
      exact h
    · intro hg
      rw [Subgroup.mem_normalizer_iff]
      intro b
      obtain ⟨a, rfl⟩ := e.surjective b
      rw [← map_inv, ← map_mul, ← map_mul, hmem, hmem]
      exact Subgroup.mem_normalizer_iff.mp hg a
  change ggAutomizer (⊤ : Subgroup H) E =
    (ggAutomizer (⊤ : Subgroup G) A).map (MulAut.congr θ).toMonoidHom
  refine le_antisymm (fun β hβ => ?_) (fun β hβ => ?_)
  · obtain ⟨h, -, hh, hβ⟩ := mem_ggAutomizer_iff.mp hβ
    let g := e.symm h
    have hg : g ∈ Subgroup.normalizer (A : Set G) :=
      (hnorm g).mp (by simpa only [g, MulEquiv.apply_symm_apply] using hh)
    let α : MulAut A := (MulAut.congr θ).symm β
    have hα : α ∈ ggAutomizer (⊤ : Subgroup G) A := by
      refine mem_ggAutomizer_iff.mpr ⟨g, Subgroup.mem_top g, hg, fun a => ?_⟩
      apply e.injective
      have heq : θ (α a) = β (θ a) := by
        change θ (θ.symm (β (θ a))) = _
        exact θ.apply_symm_apply _
      rw [← hθ, heq, hβ, hθ]
      simp only [g, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_map.mpr ⟨α, hα, (MulAut.congr θ).apply_symm_apply β⟩
  · obtain ⟨α, hα, rfl⟩ := Subgroup.mem_map.mp hβ
    obtain ⟨g, -, hg, hαg⟩ := mem_ggAutomizer_iff.mp hα
    refine mem_ggAutomizer_iff.mpr ⟨e g, Subgroup.mem_top _, (hnorm g).mpr hg, fun b => ?_⟩
    obtain ⟨a, rfl⟩ := θ.surjective b
    simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
      MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hθ, hθ, hαg, map_mul, map_mul, map_inv]

theorem card_ggAutomizer_top_map_equiv {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (A : Subgroup G) :
    Nat.card (ggAutomizer (⊤ : Subgroup H) (A.map e.toMonoidHom)) =
      Nat.card (ggAutomizer (⊤ : Subgroup G) A) := by
  rw [ggAutomizer_top_map_equiv, Subgroup.card_map_of_injective (MulAut.congr _).injective]


theorem map_range_ggGamma_of_split_model {G R : Type} [Group G] [Group R]
    {Bs K : Subgroup G} {z : G} (e : K ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hsplit : Bs = Subgroup.zpowers z ⊔ Bs ⊓ K) :
    (ggGamma K hN).range.map (MulAut.congr e).toMonoidHom =
      ((Bs.subgroupOf K).map e.toMonoidHom).map (MulAut.conj : R →* MulAut R) := by
  let Z := Subgroup.zpowers z
  let E := Bs ⊓ K
  have hZBs : Z ≤ Bs := by change Subgroup.zpowers z ≤ Bs; rw [← hker]; exact inf_le_left
  have hZK : Z ≤ Subgroup.centralizer (K : Set G) := by
    change Subgroup.zpowers z ≤ Subgroup.centralizer (K : Set G)
    rw [← hker]
    exact inf_le_right
  have hEK : E ≤ K := inf_le_right
  have hEBs : E ≤ Bs := inf_le_left
  have hcomm : ∀ x ∈ Z, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    ((Subgroup.mem_centralizer_iff.mp (hZK hx)) y (hEK hy)).symm
  have hγ : ∀ (k : K) (hk : (k : G) ∈ Bs),
      ggGamma K hN ⟨k, hk⟩ = MulAut.conj k := by
    intro k hk
    ext y
    simp only [ggGamma_coe, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  have hconj : ∀ k : K, MulAut.congr e (MulAut.conj k) = MulAut.conj (e k) := by
    intro k
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  ext α
  constructor
  · rintro ⟨β, ⟨b, rfl⟩, rfl⟩
    have hb : (b : G) ∈ Z ⊔ E := by rw [← hsplit]; exact b.property
    obtain ⟨x, hx, y, hy, hxy⟩ := (CFSG.GH74.E2.mem_sup_iff_of_commute hcomm).mp hb
    have hyBs : y ∈ Bs := hEBs hy
    have hyK : y ∈ K := hEK hy
    have hbxy : b = (⟨x, hZBs hx⟩ : Bs) * ⟨y, hyBs⟩ := Subtype.ext hxy.symm
    have hγx : ggGamma K hN ⟨x, hZBs hx⟩ = 1 := (ggGamma_eq_one_iff K hN _).mpr (hZK hx)
    simp only [MulEquiv.coe_toMonoidHom]
    rw [hbxy, map_mul, hγx, one_mul, hγ ⟨y, hyK⟩ hyBs, hconj]
    exact Subgroup.mem_map.mpr ⟨e ⟨y, hyK⟩,
      Subgroup.mem_map_of_mem e.toMonoidHom hyBs, rfl⟩
  · rintro ⟨r, ⟨k, hk, rfl⟩, rfl⟩
    have hkBs : (k : G) ∈ Bs := Subgroup.mem_subgroupOf.mp hk
    refine Subgroup.mem_map.mpr ⟨ggGamma K hN ⟨k, hkBs⟩, ⟨⟨k, hkBs⟩, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [hγ k hkBs, hconj]


theorem inner_subgroup_eq_bstar_subgroupOf {G : Type} [Group G] {p : ℕ}
    {Bs K : Subgroup G} (T : Subgroup K)
    (hZ : Function.Injective (MulAut.conj : K →* MulAut K))
    (hBs : CFSG.Open.IsElemAbelian p Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hA : T.map (MulAut.conj : K →* MulAut K) = (ggGamma K hN).range)
    (hT : ∀ t ∈ T, t ^ p = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) :
    T = Bs.subgroupOf K := by
  letI : IsMulCommutative Bs := hBs.1
  have hcomm : ∀ a ∈ (ggGamma K hN).range, ∀ b ∈ (ggGamma K hN).range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact mul_comm' a b
  ext t
  constructor
  · intro ht
    have htA : MulAut.conj t ∈ (ggGamma K hN).range := by
      rw [← hA]
      exact Subgroup.mem_map_of_mem _ ht
    have hfix : ∀ b : Bs, ggGamma K hN b t = t := by
      intro b
      apply hZ
      rw [← CFSG.mulAut_conj_mul_inv,
        hcomm _ ⟨b, rfl⟩ _ htA, mul_inv_cancel_right]
    have htC : (t : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h := congrArg Subtype.val (hfix ⟨b, hb⟩)
      simp only [ggGamma_coe] at h
      calc b * (t : G) = (b * (t : G) * b⁻¹) * b := by group
        _ = (t : G) * b := by rw [h]
    exact hSC t htC (congrArg Subtype.val (hT t ht))
  · intro ht
    have hγ : ggGamma K hN ⟨t, ht⟩ = MulAut.conj t := by
      ext x
      simp only [ggGamma_coe, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    have htA : MulAut.conj t ∈ T.map (MulAut.conj : K →* MulAut K) := by
      rw [hA, ← hγ]
      exact ⟨⟨t, ht⟩, rfl⟩
    obtain ⟨u, hu, hut⟩ := Subgroup.mem_map.mp htA
    exact hZ hut ▸ hu

theorem bstar_split_of_inner_subgroup {G : Type} [Group G] {p : ℕ}
    {Bs K : Subgroup G} {z : G} (T : Subgroup K)
    (hZ : Function.Injective (MulAut.conj : K →* MulAut K))
    (hBs : CFSG.Open.IsElemAbelian p Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hA : T.map (MulAut.conj : K →* MulAut K) = (ggGamma K hN).range)
    (hT : ∀ t ∈ T, t ^ p = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z) :
    T.map K.subtype = Bs ⊓ K ∧
      Bs = Subgroup.zpowers z ⊔ T.map K.subtype ∧
      Subgroup.zpowers z ⊓ T.map K.subtype = ⊥ := by
  have hTE := inner_subgroup_eq_bstar_subgroupOf T hZ hBs hN hA hT hSC
  have hmap : T.map K.subtype = Bs ⊓ K := by
    rw [hTE]
    ext b
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨hk, k.property⟩
    · intro hb
      exact ⟨⟨b, hb.2⟩, hb.1, rfl⟩
  have hZBs : Subgroup.zpowers z ≤ Bs := by rw [← hker]; exact inf_le_left
  have hTbs : ∀ t ∈ T, (t : G) ∈ Bs := by
    intro t ht
    rw [hTE] at ht
    exact ht
  have hγT : ∀ t : K, ∀ ht : (t : G) ∈ Bs,
      ggGamma K hN ⟨t, ht⟩ = MulAut.conj t := by
    intro t ht
    ext x
    simp only [ggGamma_coe, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  have hsplit : Bs = Subgroup.zpowers z ⊔ T.map K.subtype := by
    refine le_antisymm (fun b hb => ?_) (sup_le hZBs (by rw [hmap]; exact inf_le_left))
    have hbA : ggGamma K hN ⟨b, hb⟩ ∈ T.map (MulAut.conj : K →* MulAut K) := by
      rw [hA]
      exact ⟨⟨b, hb⟩, rfl⟩
    obtain ⟨t, ht, htb⟩ := Subgroup.mem_map.mp hbA
    have htBs := hTbs t ht
    let x : G := b * (t : G)⁻¹
    have hxBs : x ∈ Bs := Bs.mul_mem hb (Bs.inv_mem htBs)
    have hxγ : ggGamma K hN ⟨x, hxBs⟩ = 1 := by
      change ggGamma K hN ((⟨b, hb⟩ : Bs) * ⟨t, htBs⟩⁻¹) = 1
      rw [map_mul, map_inv, hγT, ← htb, mul_inv_cancel]
    have hxC : x ∈ Subgroup.centralizer (K : Set G) :=
      (ggGamma_eq_one_iff K hN ⟨x, hxBs⟩).mp hxγ
    have hxZ : x ∈ Subgroup.zpowers z := by rw [← hker]; exact ⟨hxBs, hxC⟩
    have htG : (t : G) ∈ T.map K.subtype := Subgroup.mem_map_of_mem K.subtype ht
    have hxSup : x ∈ Subgroup.zpowers z ⊔ T.map K.subtype :=
      (le_sup_left : Subgroup.zpowers z ≤ Subgroup.zpowers z ⊔ T.map K.subtype) hxZ
    have htSup : (t : G) ∈ Subgroup.zpowers z ⊔ T.map K.subtype :=
      (le_sup_right : T.map K.subtype ≤ Subgroup.zpowers z ⊔ T.map K.subtype) htG
    have hprod := (Subgroup.zpowers z ⊔ T.map K.subtype).mul_mem hxSup htSup
    simpa only [x, mul_assoc, inv_mul_cancel, mul_one] using hprod
  have hcenter : Subgroup.center K = ⊥ := by
    rw [← CFSG.mulAut_conj_ker]
    exact (MonoidHom.ker_eq_bot_iff (MulAut.conj : K →* MulAut K)).mpr hZ
  have hdisj : Subgroup.zpowers z ⊓ T.map K.subtype = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    rw [hmap] at hx
    have hxC : x ∈ Subgroup.centralizer (K : Set G) := by
      have hle : Subgroup.zpowers z ≤ Subgroup.centralizer (K : Set G) := by
        rw [← hker]
        exact inf_le_right
      exact hle hx.1
    have hxZ : (⟨x, hx.2.2⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      exact fun k => Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC) k k.property)
    rw [hcenter, Subgroup.mem_bot] at hxZ
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxZ)
  exact ⟨hmap, hsplit, hdisj⟩

theorem selfCentralizing_torus_of_split_model {G R : Type} [Group G] [Group R]
    {Bs K : Subgroup G} {z : G} (e : K ≃* R)
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hsplit : Bs = Subgroup.zpowers z ⊔ Bs ⊓ K)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs) :
    ∀ Z : R, (∀ Y ∈ (Bs.subgroupOf K).map e.toMonoidHom, Z * Y = Y * Z) →
      Z ^ 3 = 1 → Z ∈ (Bs.subgroupOf K).map e.toMonoidHom := by
  intro Z hZ hZ3
  let k : K := e.symm Z
  have hzK : z ∈ Subgroup.centralizer (K : Set G) := by
    have hz : z ∈ Bs ⊓ Subgroup.centralizer (K : Set G) := by
      rw [hker]
      exact Subgroup.mem_zpowers z
    exact hz.2
  have hBsC : Bs ≤ Subgroup.centralizer ({(k : G)} : Set G) := by
    rw [hsplit]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hzK) k k.property).symm
    · intro b hb
      have hbE : e ⟨b, hb.2⟩ ∈ (Bs.subgroupOf K).map e.toMonoidHom :=
        Subgroup.mem_map_of_mem e.toMonoidHom hb.1
      have hk : k * (⟨b, hb.2⟩ : K) = (⟨b, hb.2⟩ : K) * k := by
        apply e.injective
        simpa only [k, map_mul, MulEquiv.apply_symm_apply] using hZ _ hbE
      exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hk).symm
  have hk3 : k ^ 3 = 1 := by
    apply e.injective
    simpa only [k, map_pow, map_one, MulEquiv.apply_symm_apply] using hZ3
  have hkBs : (k : G) ∈ Bs := hBstar k
    (Subgroup.mem_centralizer_iff.mpr fun b hb =>
      Subgroup.mem_centralizer_singleton_iff.mp (hBsC hb))
    (congrArg Subtype.val hk3)
  exact Subgroup.mem_map.mpr ⟨k, hkBs, e.apply_symm_apply Z⟩

end CFSG.StandardType

end
