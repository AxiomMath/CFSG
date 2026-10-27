module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModM10
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModSecBase
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.ModPack28
public import CFSG.Quasithin.EmptyFaithful.S152XS5

public section

namespace CFSG.Quasithin.F53Mod

open CFSG.Open CFSG.QuasithinUnique Equiv

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_conj_le_syl_of_isPGroup {B : Subgroup (Perm (Fin 5))} (hp : IsPGroup 2 B) :
    ∃ g : Perm (Fin 5), B.map (MulAut.conj g).toMonoidHom ≤ S5Syl := by
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hcard : Nat.card (Q : Subgroup (Perm (Fin 5))) = 8 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    have h120 : (Nat.factorial 5).factorization 2 = 3 := by
      rw [Nat.factorization_def _ Nat.prime_two]
      have : Nat.factorial 5 = 2 ^ 3 * 15 := by decide
      rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [h120]; norm_num
  obtain ⟨g, hg⟩ := exists_conj_S5Syl hcard
  refine ⟨g⁻¹, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  have hbQ : b ∈ (Q : Subgroup (Perm (Fin 5))) := hQ hb
  rw [hg] at hbQ
  obtain ⟨s, hs, hsb⟩ := hbQ
  have : (MulAut.conj g⁻¹).toMonoidHom b = s := by
    rw [← hsb]
    simp [MulAut.conj_apply, mul_assoc]
  rw [this]
  exact hs

section Section

variable {X Y : Subgroup G} (hs : IsSec X ⊥ Y) (θ : ↥X →* Perm (Fin 5))
  (hθ : Function.Surjective θ) (hk : θ.ker ≤ (cSecIn X ⊥ Y).subgroupOf X)

omit [Finite G] in
theorem proj_injective_bot : Function.Injective hs.proj := by
  intro x y h
  have := (hs.proj_eq_proj_iff x y).mp h
  rw [Subgroup.mem_bot] at this
  exact Subtype.ext (inv_mul_eq_one.mp this)

theorem mem_fixW_range_iff {S : Subgroup G} (hSX : S ≤ X) (x : ↥Y) :
    hs.proj x ∈ fixW (secModule hs θ hθ hk) (θ.comp (Subgroup.inclusion hSX)).range ↔
      ∀ a ∈ S, a * (x : G) * a⁻¹ = x := by
  constructor
  · intro h a ha
    have h1 := h (θ.comp (Subgroup.inclusion hSX) ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩
    have h2 : (secModule hs θ hθ hk).act (θ ⟨a, hSX ha⟩) (hs.proj x) = hs.proj (hs.conjN ⟨a, hSX ha⟩ x) :=
      secModule_act_proj hs θ hθ hk ⟨a, hSX ha⟩ x
    have h3 : hs.proj (hs.conjN ⟨a, hSX ha⟩ x) = hs.proj x := h2.symm.trans h1
    have h4 := proj_injective_bot hs h3
    exact congrArg Subtype.val h4
  · rintro h _ ⟨a, rfl⟩
    have h2 : (secModule hs θ hθ hk).act (θ (Subgroup.inclusion hSX a)) (hs.proj x) =
        hs.proj (hs.conjN (Subgroup.inclusion hSX a) x) :=
      secModule_act_proj hs θ hθ hk _ x
    show (secModule hs θ hθ hk).act (θ (Subgroup.inclusion hSX a)) (hs.proj x) = hs.proj x
    rw [h2]
    congr 1
    exact Subtype.ext (h a a.2)

theorem index_fixW_range {S : Subgroup G} (hSX : S ≤ X) :
    (fixW (secModule hs θ hθ hk) (θ.comp (Subgroup.inclusion hSX)).range).index =
      (Y ⊓ Subgroup.centralizer (S : Set G)).relIndex Y := by
  let pM : ↥Y →* (secModule hs θ hθ hk).W := hs.proj
  have hbij : Function.Bijective pM := ⟨proj_injective_bot hs, hs.proj_surjective⟩
  have himg : fixW (secModule hs θ hθ hk) (θ.comp (Subgroup.inclusion hSX)).range =
      ((Y ⊓ Subgroup.centralizer (S : Set G)).subgroupOf Y).map pM := by
    ext w
    obtain ⟨x, rfl⟩ : ∃ x : ↥Y, pM x = w := hs.proj_surjective w
    refine (mem_fixW_range_iff hs θ hθ hk hSX x).trans ?_
    rw [Subgroup.mem_map]
    constructor
    · intro h
      refine ⟨x, ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
      refine ⟨x.2, fun a ha => ?_⟩
      have := h a ha
      calc a * (x : G) = a * x * a⁻¹ * a := by group
        _ = x * a := by rw [this]
    · rintro ⟨x', hx', hxx'⟩ a ha
      have hx : x' = x := proj_injective_bot hs hxx'
      subst hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hx'
      have := hx'.2 a ha
      calc a * (x' : G) * a⁻¹ = x' * a * a⁻¹ := by rw [this]
        _ = x' := by group
  rw [himg, Subgroup.index_map_of_bijective hbij]
  rfl

end Section

theorem modPack28_of_theta (X Q P R Y A : Subgroup G) (θ : ↥X →* Perm (Fin 5))
    (hθ : Function.Surjective θ) (hker : ∀ (x : G) (hx : x ∈ X), θ ⟨x, hx⟩ = 1 ↔ x ∈ Q)
    (hPX : P ≤ X) (hPS : ∀ (p : G) (hp : p ∈ P), θ ⟨p, hPX hp⟩ ∈ S5Syl)
    (hQR : Q ≤ R) (hRP : R ≤ P) (hRel : Q.relIndex R = 4)
    (hY : IsElemAbelian 2 Y) (hXN : X ≤ Subgroup.normalizer (Y : Set G))
    (hC : X ⊓ Subgroup.centralizer (Y : Set G) = Q)
    (hAR : A ≤ R) (hA : IsElemAbelian 2 A) (hAQ : ¬ A ≤ Q)
    (hoff : (Y ⊓ Subgroup.centralizer (A : Set G)).relIndex Y ≤ (A ⊓ Q).relIndex A) :
    (∀ g ∈ R, g ^ 2 ∈ Q) ∧
      ¬ (Y ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.centralizer (X : Set G)) := by
  have hRX : R ≤ X := hRP.trans hPX
  have hAX : A ≤ X := hAR.trans hRX
  have hQX : Q ≤ X := hQR.trans hRX
  have hYcomm := isMulCommutative_subgroup_iff.mp hY.1
  have hs : IsSec X ⊥ Y :=
    { le := bot_le
      normN := hXN
      normL := fun x _ => by
        rw [Subgroup.mem_normalizer_iff]
        intro h
        simp only [Subgroup.mem_bot]
        constructor
        · rintro rfl; simp
        · intro h1
          have : h = x⁻¹ * (x * h * x⁻¹) * x := by group
          rw [this, h1]; simp
      comm := fun x hx y hy => by
        rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
        exact (hYcomm x hx y hy)
      sq := fun x hx => by rw [Subgroup.mem_bot]; exact hY.2 x hx }
  have hcent : ∀ (f : G) (hf : f ∈ X), (∀ y ∈ Y, f * y * f⁻¹ * y⁻¹ ∈ (⊥ : Subgroup G)) ↔
      θ ⟨f, hf⟩ = 1 := by
    intro f hf
    rw [hker f hf, ← hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      refine ⟨hf, fun y hy => ?_⟩
      have := h y hy
      rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    · rintro ⟨-, h⟩ y hy
      rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact (h y hy).symm
  have hk : θ.ker ≤ (cSecIn X ⊥ Y).subgroupOf X := by
    intro f hf
    rw [Subgroup.mem_subgroupOf]
    refine (mem_cSecIn_iff (fun x _ => ?_)).mpr ⟨f.2, (hcent f f.2).mpr (MonoidHom.mem_ker.mp hf)⟩
    exact hs.normL ‹_›
  set M := secModule hs θ hθ hk with hM
  have hfaith : M.Faithful := by
    rw [hM, secModule_faithful_iff]
    intro f hf
    rw [MonoidHom.mem_ker]
    obtain ⟨hfX, hfc⟩ := (mem_cSecIn_iff (fun x _ => hs.normL ‹_›)).mp (Subgroup.mem_subgroupOf.mp hf)
    exact (hcent f hfX).mp hfc
  set fA : ↥A →* Perm (Fin 5) := θ.comp (Subgroup.inclusion hAX) with hfA
  have hkerA : fA.ker = (A ⊓ Q).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    show θ ⟨a.1, hAX a.2⟩ = 1 ↔ _
    rw [hker a.1 (hAX a.2)]
    exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩
  have hcardA : (A ⊓ Q).relIndex A = Nat.card fA.range := by
    rw [Subgroup.relIndex, ← hkerA]
    exact Subgroup.index_ker fA
  have hexpA : ∀ x ∈ fA.range, x * x = 1 := by
    rintro _ ⟨a, rfl⟩
    show θ ⟨a.1, hAX a.2⟩ * θ ⟨a.1, hAX a.2⟩ = 1
    rw [← map_mul]
    have : (⟨a.1, hAX a.2⟩ : ↥X) * ⟨a.1, hAX a.2⟩ = 1 :=
      Subtype.ext (by simpa [pow_two] using hA.2 a.1 a.2)
    rw [this, map_one]
  have hneA : fA.range ≠ ⊥ := by
    intro h
    obtain ⟨a, haA, haQ⟩ := IsConcreteLE.not_le_iff_exists.mp hAQ
    have h1 : fA ⟨a, haA⟩ ∈ fA.range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact haQ ((hker a (hAX haA)).mp h1)
  have hSA : fA.range ≤ S5Syl := by
    rintro _ ⟨a, rfl⟩
    exact hPS a.1 (hRP (hAR a.2))
  have hoffM : (fixW M fA.range).index ≤ Nat.card fA.range := by
    rw [hM, index_fixW_range hs θ hθ hk hAX]
    exact hoff.trans hcardA.le
  refine ⟨?_, ?_⟩
  ·
    set fR : ↥R →* Perm (Fin 5) := θ.comp (Subgroup.inclusion hRX) with hfR
    have hkerR : fR.ker = Q.subgroupOf R := by
      ext a
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      show θ ⟨a.1, hRX a.2⟩ = 1 ↔ _
      exact hker a.1 (hRX a.2)
    have hcardR : Nat.card fR.range = 4 := by
      rw [← Subgroup.index_ker, hkerR]
      exact hRel
    have hBR : fA.range ≤ fR.range := by
      rintro _ ⟨a, rfl⟩
      exact ⟨⟨a.1, hAR a.2⟩, rfl⟩
    have hexp := exp_two_of_offender M hfaith hBR hcardR hexpA hneA hoffM
    intro g hg
    have h1 : fR ⟨g, hg⟩ ∈ fR.range := ⟨_, rfl⟩
    have h2 := hexp _ h1
    have h3 : θ ⟨g * g, X.mul_mem (hRX hg) (hRX hg)⟩ = 1 := by
      have h4 : θ ⟨g, hRX hg⟩ * θ ⟨g, hRX hg⟩ = 1 := h2
      rw [← map_mul] at h4
      exact h4
    rw [pow_two]
    exact (hker _ _).mp h3
  · obtain ⟨v, hvS, hvn⟩ := m10 M hfaith hSA hexpA hneA hoffM
    obtain ⟨y, rfl⟩ : ∃ y : ↥Y, (hs.proj y : M.W) = v := hs.proj_surjective v
    have hyP : ∀ p ∈ P, p * (y : G) = y * p := by
      intro p hp
      have h1 := hvS (θ ⟨p, hPX hp⟩) (hPS p hp)
      have h2 : M.act (θ ⟨p, hPX hp⟩) (hs.proj y) = hs.proj (hs.conjN ⟨p, hPX hp⟩ y) :=
        secModule_act_proj hs θ hθ hk ⟨p, hPX hp⟩ y
      have h3 : hs.proj (hs.conjN ⟨p, hPX hp⟩ y) = hs.proj y := h2.symm.trans h1
      have h4 := congrArg Subtype.val (proj_injective_bot hs h3)
      have h5 : p * (y : G) * p⁻¹ = y := h4
      rw [mul_inv_eq_iff_eq_mul] at h5
      exact h5
    intro hle
    have hmem : (y : G) ∈ Y ⊓ Subgroup.centralizer (P : Set G) :=
      Subgroup.mem_inf.mpr ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun p hp => hyP p hp⟩
    have hcX := Subgroup.mem_centralizer_iff.mp (hle hmem)
    apply hvn
    intro σ _
    obtain ⟨h, rfl⟩ := hθ σ
    have h2 : M.act (θ h) (hs.proj y) = hs.proj (hs.conjN h y) := secModule_act_proj hs θ hθ hk h y
    rw [h2]
    congr 1
    apply Subtype.ext
    show (h : G) * y * (h : G)⁻¹ = y
    rw [mul_inv_eq_iff_eq_mul]
    exact hcX h h.2

end CFSG.Quasithin.F53Mod

namespace CFSG.Quasithin.F53.Stellmacher

open CFSG.Quasithin.F53Mod CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152X Equiv

theorem modPack28_holds : ModPack28 := by
  intro G _ _ X Q P R Y A hQ hq hP hQR hRP _ hRel hY hYQ hXN hC hAR hA hAQ hoff
  obtain ⟨φ⟩ := hq
  obtain ⟨hPX, hP2, -⟩ := hP
  have hker0 : ∀ (x : G) (hx : x ∈ X), piS5 X φ ⟨x, hx⟩ = 1 ↔ x ∈ Q := by
    intro x hx
    rw [hQ]
    have h1 : piS5 X φ ⟨x, hx⟩ = 1 ↔ (⟨x, hx⟩ : ↥X) ∈ CFSG.Open.pCore 2 ↥X := by
      rw [← piS5_ker X φ, MonoidHom.mem_ker]
    rw [h1]
    constructor
    · intro h
      exact ⟨⟨x, hx⟩, h, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = ⟨x, hx⟩ := Subtype.ext hyx
      rwa [this] at hy
  set fP : ↥P →* Perm (Fin 5) := (piS5 X φ).comp (Subgroup.inclusion hPX) with hfP
  have hpg : IsPGroup 2 fP.range := hP2.of_surjective fP.rangeRestrict fP.rangeRestrict_surjective
  obtain ⟨g, hg⟩ := exists_conj_le_syl_of_isPGroup hpg
  set θ : ↥X →* Perm (Fin 5) := (MulAut.conj g).toMonoidHom.comp (piS5 X φ) with hθdef
  have hθ : Function.Surjective θ :=
    (MulAut.conj g).surjective.comp (piS5_surj X φ)
  refine modPack28_of_theta X Q P R Y A θ hθ ?_ hPX ?_ hQR hRP hRel hY hXN hC hAR hA hAQ hoff
  · intro x hx
    rw [← hker0 x hx]
    show (MulAut.conj g) (piS5 X φ ⟨x, hx⟩) = 1 ↔ _
    exact (MulAut.conj g).map_eq_one_iff
  · intro p hp
    exact hg ⟨fP ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩, rfl⟩

end CFSG.Quasithin.F53.Stellmacher
