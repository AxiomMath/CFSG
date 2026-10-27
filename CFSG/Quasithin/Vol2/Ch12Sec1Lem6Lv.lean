module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem6Gen
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem6Par
public import CFSG.Quasithin.Vol2.KGFactH91B

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix
open CFSG.ComponentClassification.CatalogueBGraphForm
open scoped Matrix commutatorElement

namespace Sec1216Lv

variable {G : Type} [Group G]

theorem eq_bot_of_perfect_two [Finite G] {X : Subgroup G} (hX : ⁅X, X⁆ = X) (h2 : IsPGroup 2 X) :
    X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).2 hne
  have : Group.IsNilpotent ↥X := h2.isNilpotent
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥X).ne
    (Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hX))

theorem perfect_le_of_le_sup_two [Finite G] {L N P : Subgroup G} (hLp : ⁅L, L⁆ = L)
    (hNL : N ≤ L) (hNn : ∀ l ∈ L, ∀ x ∈ N, l * x * l⁻¹ ∈ N) (hP : IsPGroup 2 P) (hPL : P ≤ L)
    (hle : L ≤ N ⊔ P) : L ≤ N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNnormal : (N.subgroupOf L).Normal := ⟨fun x hx l => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hNn l l.2 x hx⟩
  have hQ2 : IsPGroup 2 (↥L ⧸ N.subgroupOf L) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hxN : x ∈ N.subgroupOf L ⊔ P.subgroupOf L := by
      rw [← Subgroup.subgroupOf_sup hNL hPL]
      exact hle x.2
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hxN
    have hPpL : IsPGroup 2 (P.subgroupOf L) :=
      hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPL).symm
    obtain ⟨k, hk⟩ := hPpL ⟨z, hz⟩
    refine ⟨k, ?_⟩
    have e : (QuotientGroup.mk x : ↥L ⧸ N.subgroupOf L) = QuotientGroup.mk z := by
      rw [← hyz, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff y).mpr hy, one_mul]
    rw [e, ← QuotientGroup.mk_pow]
    have : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [this, QuotientGroup.mk_one]
  have : Group.IsNilpotent (↥L ⧸ N.subgroupOf L) := hQ2.isNilpotent
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLp
  have hsub : Subsingleton (↥L ⧸ N.subgroupOf L) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent (↥L ⧸ N.subgroupOf L) ‹_›
  intro x hx
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : ↥L) : ↥L ⧸ N.subgroupOf L) = 1 := Subsingleton.elim _ _
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨x, hx⟩ : ↥L)).mp h1)

theorem mem_cComp_of_hom [Finite G] {X T : Subgroup G} {S : Type} [Group S] [IsSimpleGroup S]
    (hX : ⁅X, X⁆ = X) (hX1 : X ≠ ⊥) (hTX : T ≤ Subgroup.normalizer (X : Set G)) (f : ↥X →* S)
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) : X ∈ cComp (X ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hX1, hX, A3.subnormal_of_normal le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hTX)), fun K hKX hK1 hKp hKs => ?_⟩
  have hKX' : IsSubnormal K X := A3.subnormal_of_le_of_le hKs hKX.le le_sup_left
  obtain ⟨P, hPX, hPn, hKP⟩ := A3.subnormal_exists_normal_of_lt hKX' hKX
  have hPX' : P ≤ X := hPX.le
  have hfP : ((P.subgroupOf X).map f).Normal := Subgroup.Normal.map hPn f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((P.subgroupOf X).map f) with h | h
  ·
    apply hK1
    refine eq_bot_of_perfect_two hKp fun k => ?_
    have hkX : (k : G) ∈ X := hKX.le k.2
    have hk : (⟨k, hkX⟩ : ↥X) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      have : f ⟨k, hkX⟩ ∈ (P.subgroupOf X).map f := ⟨⟨k, hkX⟩, hKP k.2, rfl⟩
      rwa [h, Subgroup.mem_bot] at this
    obtain ⟨j, hj⟩ := hker ⟨_, hk⟩
    refine ⟨j, Subtype.ext ?_⟩
    have := congrArg (fun x : ↥f.ker => ((x : ↥X) : G)) hj
    simpa using this
  ·
    have hXP : X ≤ P := by
      refine perfect_le_of_le_sup_two hX hPX' (fun l hl p hp => ?_) (hker.map X.subtype)
        (Subgroup.map_subtype_le _) ?_
      · exact hPn.conj_mem ⟨p, hPX' hp⟩ hp ⟨l, hl⟩
      · intro x hx
        have hfx : f ⟨x, hx⟩ ∈ (P.subgroupOf X).map f := by rw [h]; exact Subgroup.mem_top _
        obtain ⟨p, hp, hpx⟩ := hfx
        have hk : p⁻¹ * ⟨x, hx⟩ ∈ f.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hpx, inv_mul_cancel]
        have e : x = (p : G) * ((p⁻¹ * ⟨x, hx⟩ : ↥X) : G) := by simp
        rw [e]
        exact Subgroup.mul_mem_sup hp ⟨_, hk, rfl⟩
    exact hPX.not_ge hXP

@[expose] def lv (L : Subgroup G) (v : G) : Subgroup G :=
  perfectCore (L ⊓ Subgroup.centralizer ({v} : Set G))

theorem lv_le_L (L : Subgroup G) (v : G) : lv L v ≤ L := (perfectCore_le _).trans inf_le_left

theorem lv_le_centralizer (L : Subgroup G) (v : G) :
    lv L v ≤ Subgroup.centralizer ({v} : Set G) :=
  (perfectCore_le _).trans inf_le_right

theorem lv_perfect [Finite G] (L : Subgroup G) (v : G) : ⁅lv L v, lv L v⁆ = lv L v :=
  perfectCore_perfect _

theorem le_normalizer_lv {L X : Subgroup G} {v : G}
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) (hXv : X ≤ Subgroup.centralizer ({v} : Set G)) :
    X ≤ Subgroup.normalizer (lv L v : Set G) := fun _ hx =>
  normalizer_le_normalizer_perfectCore _ (Sec1216Gen.mem_normalizer_inf (hXL hx)
    (Subgroup.le_normalizer (hXv hx)))

structure Setting [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ) (v : G) where
  C₁ : KGH91.NatCoord L V₁ n
  C₂ : KGH91.NatCoord L V₂ n
  hd : ∀ l, C₂.ρ l = slGraphAut n (ZMod 2) (C₁.ρ l)
  ctx : Sec1216Gen.Ctx0 T L V V₁ V₂ n (KGH91.pairing C₁ C₂) v

namespace Setting

variable [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {v : G} (S : Setting T L V V₁ V₂ n v)
include S

theorem rank : n = 4 ∨ n = 5 := S.ctx.hyp.rank

theorem three_le : 3 ≤ n - 1 := by rcases S.rank with h | h <;> omega

theorem one_add : 1 + (n - 1) = n := by rcases S.rank with h | h <;> omega

theorem three_le' : 3 ≤ n := by rcases S.rank with h | h <;> omega

theorem x₀_ne : S.C₁.E v ≠ 0 := fun h => S.ctx.v_ne_one (S.C₁.eq_one_of_E S.ctx.v_mem_V₁ h)

theorem mem_centralizer_iff (l : ↥L) :
    (l : G) ∈ Subgroup.centralizer ({v} : Set G) ↔
      S.C₁.ρ l ∈ VecStab.vecStab (S.C₁.E v) := by
  rw [VecStab.mem_vecStab, ← S.C₁.conj l v S.ctx.v_mem_V₁, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [h, mul_inv_cancel_right]
  · intro h
    have h1 := S.C₁.inj _ (S.C₁.conj_mem l S.ctx.v_mem_V₁) _ S.ctx.v_mem_V₁ h
    calc (l : G) * v = ((l : G) * v * (l : G)⁻¹) * l := by group
      _ = v * l := by rw [h1]

theorem map_inf : ((L ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf L).map S.C₁.ρ =
    VecStab.vecStab (S.C₁.E v) := by
  ext g
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact (S.mem_centralizer_iff l).mp (Subgroup.mem_subgroupOf.mp hl).2
  · intro hg
    obtain ⟨l, rfl⟩ := S.C₁.ρ_surj g
    exact ⟨l, Subgroup.mem_subgroupOf.mpr ⟨l.2, (S.mem_centralizer_iff l).mpr hg⟩, rfl⟩

theorem exists_mem_lv {g : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hg : g ∈ VecStab.vecStab (S.C₁.E v)) : ∃ l : ↥L, (l : G) ∈ lv L v ∧ S.C₁.ρ l = g := by
  have h1 : (perfectCore ((L ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf L)).map S.C₁.ρ =
      VecStab.vecStab (S.C₁.E v) := by
    rw [map_perfectCore, S.map_inf, perfectCore_eq_self_of_perfect
      (VecStab.commutator_eq S.three_le S.one_add S.x₀_ne)]
  have h2 : (perfectCore ((L ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf L)).map
      L.subtype = lv L v := by
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    rfl
  rw [← h1] at hg
  obtain ⟨l, hl, rfl⟩ := hg
  exact ⟨l, h2 ▸ ⟨l, hl, rfl⟩, rfl⟩

theorem T₁_le_normalizer_lv :
    T ⊓ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (lv L v : Set G) :=
  le_normalizer_lv S.ctx.T₁_le_NL S.ctx.T₁_le

theorem V_le_normalizer_lv : V ≤ Subgroup.normalizer (lv L v : Set G) :=
  S.ctx.V_le_T₁.trans S.T₁_le_normalizer_lv

theorem mul_conj_mem {b l : G} (hb : b ∈ V) (hl : l ∈ lv L v) : b * (l * b * l⁻¹) ∈ lv L v := by
  have e : b * (l * b * l⁻¹) = b * l * b⁻¹ * l⁻¹ := by
    rw [S.ctx.inv_eq hb]
    group
  rw [e]
  exact (lv L v).mul_mem ((Subgroup.mem_normalizer_iff.mp (S.V_le_normalizer_lv hb) l).mp hl)
    ((lv L v).inv_mem hl)

theorem V₁_le_commutator : V₁ ≤ ⁅V₁, lv L v⁆ := by
  intro a ha
  obtain ⟨x, hx⟩ := VecStab.exists_not_mem_finset
    ({0, S.C₁.E v, S.C₁.E a, S.C₁.E v + S.C₁.E a} : Finset (Fin n → ZMod 2)) (by
      have h4 : ({0, S.C₁.E v, S.C₁.E a, S.C₁.E v + S.C₁.E a} :
          Finset (Fin n → ZMod 2)).card ≤ 4 := Finset.card_le_four
      have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) S.three_le'
      omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  obtain ⟨hx0, hxv, hxa, hxva⟩ := hx
  obtain ⟨A, hA₀, hA⟩ := Sec1216Gen.exists_sl_fix (y := x + S.C₁.E a) S.x₀_ne hx0 hxv
    (fun h => hxa (VecStab.eq_of_add_eq_zero h))
    (fun h => hxva (by rw [← h, add_assoc, VecStab.add_self, add_zero]))
  obtain ⟨l, hl, hlA⟩ := S.exists_mem_lv (g := A) hA₀
  have hb : S.C₁.inv x ∈ V₁ := S.C₁.inv_mem x
  have key : a = S.C₁.inv x * ((l : G) * S.C₁.inv x * (l : G)⁻¹) := by
    apply S.C₁.inj a ha _ (V₁.mul_mem hb (S.C₁.conj_mem l hb))
    rw [S.C₁.map_mul _ hb _ (S.C₁.conj_mem l hb), S.C₁.conj l _ hb, hlA, S.C₁.E_inv, hA,
      ← add_assoc, VecStab.add_self, zero_add]
  have e : S.C₁.inv x * ((l : G) * S.C₁.inv x * (l : G)⁻¹) = ⁅S.C₁.inv x, (l : G)⁆ := by
    rw [commutatorElement_def, S.ctx.inv_eq (S.ctx.V₁_le hb)]
    group
  rw [key, e]
  exact Subgroup.commutator_mem_commutator hb hl

theorem V₁_le_lv : V₁ ≤ lv L v :=
  S.V₁_le_commutator.trans (Subgroup.commutator_le.mpr fun b hb l hl => by
    rw [commutatorElement_def]
    exact (lv L v).mul_mem ((Subgroup.mem_normalizer_iff.mp
      (S.V_le_normalizer_lv (S.ctx.V₁_le hb)) l).mp hl) ((lv L v).inv_mem hl))

theorem U₂_le_lv : S.ctx.U₂ ≤ lv L v := by
  intro c hc
  have hcV : c ∈ V₂ := hc.1
  have hc0 : S.C₁.E v ⬝ᵥ S.C₂.E c = 0 := hc.2
  obtain ⟨y, hy, hy0, hyc⟩ := VecStab.exists_perp_ne S.three_le' S.x₀_ne (S.C₂.E c)
  obtain ⟨g, hg, hgy⟩ := VecStab.exists_dual' (w' := y + S.C₂.E c) S.x₀_ne hy0
    (fun h => hyc (VecStab.eq_of_add_eq_zero h)) hy (by rw [dotProduct_add, hy, hc0, add_zero])
  obtain ⟨l, hl, hlg⟩ := S.exists_mem_lv hg
  have hd : S.C₂.inv y ∈ V₂ := S.C₂.inv_mem y
  have key : c = S.C₂.inv y * ((l : G) * S.C₂.inv y * (l : G)⁻¹) := by
    apply S.C₂.inj c hcV _ (V₂.mul_mem hd (S.C₂.conj_mem l hd))
    rw [S.C₂.map_mul _ hd _ (S.C₂.conj_mem l hd), S.C₂.conj l _ hd, S.hd, hlg, S.C₂.E_inv, hgy,
      ← add_assoc, VecStab.add_self, zero_add]
  rw [key]
  exact S.mul_conj_mem (S.ctx.V₂_le hd) hl

theorem mem_zpowers_of_fixed {a : G} (ha : a ∈ V₁) (h : ∀ l ∈ lv L v, l * a * l⁻¹ = a) :
    a ∈ Subgroup.zpowers v := by
  rw [S.ctx.mem_zpowers_iff]
  by_contra hcon
  push Not at hcon
  obtain ⟨ha1, hav⟩ := hcon
  have hE0 : S.C₁.E a ≠ 0 := fun h0 => ha1 (S.C₁.eq_one_of_E ha h0)
  have hEv : S.C₁.E a ≠ S.C₁.E v := fun h' => hav (S.C₁.inj a ha v S.ctx.v_mem_V₁ h')
  obtain ⟨y, hy⟩ := VecStab.exists_not_mem_finset
    ({0, S.C₁.E v, S.C₁.E a} : Finset (Fin n → ZMod 2)) (by
      have h3 : ({0, S.C₁.E v, S.C₁.E a} : Finset (Fin n → ZMod 2)).card ≤ 3 :=
        Finset.card_le_three
      have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) S.three_le'
      omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  obtain ⟨hy0, hyv, hya⟩ := hy
  obtain ⟨A, hA₀, hA⟩ := Sec1216Gen.exists_sl_fix S.x₀_ne hE0 hEv hy0 hyv
  obtain ⟨l, hl, hlA⟩ := S.exists_mem_lv hA₀
  have h1 := congrArg S.C₁.E (h l hl)
  rw [S.C₁.conj l a ha, hlA, hA] at h1
  exact hya h1

theorem eq_one_of_fixed {c : G} (hc : c ∈ S.ctx.U₂) (h : ∀ l ∈ lv L v, l * c * l⁻¹ = c) :
    c = 1 := by
  by_contra hc1
  have hcV : c ∈ V₂ := hc.1
  have hc0 : S.C₁.E v ⬝ᵥ S.C₂.E c = 0 := hc.2
  have hE0 : S.C₂.E c ≠ 0 := fun h0 => hc1 (S.C₂.eq_one_of_E hcV h0)
  obtain ⟨y, hy, hy0, hyc⟩ := VecStab.exists_perp_ne S.three_le' S.x₀_ne (S.C₂.E c)
  obtain ⟨g, hg, hgc⟩ := VecStab.exists_dual' S.x₀_ne hE0 hy0 hc0 hy
  obtain ⟨l, hl, hlg⟩ := S.exists_mem_lv hg
  have h1 := congrArg S.C₂.E (h l hl)
  rw [S.C₂.conj l c hcV, S.hd, hlg, hgc] at h1
  exact hyc h1

theorem conj_mem_U₂ {m : G} (hm : m ∈ Subgroup.normalizer (L : Set G))
    (hm1 : m ∈ Subgroup.normalizer (V₁ : Set G)) (hmv : m ∈ Subgroup.centralizer ({v} : Set G))
    {c : G} (hc : c ∈ S.ctx.U₂) : m * c * m⁻¹ ∈ S.ctx.U₂ := by
  refine ⟨S.ctx.conj_V₂ hm hm1 hc.1, ?_⟩
  have hmv' : m * v * m⁻¹ = v := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hmv
    rw [hmv, mul_inv_cancel_right]
  have h1 := S.ctx.β_conj hm hm1 S.ctx.v_mem_V₁ hc.1
  rw [hmv'] at h1
  rw [h1]
  exact hc.2

theorem lv_conj_mem_U₂ {l c : G} (hl : l ∈ lv L v) (hc : c ∈ S.ctx.U₂) :
    l * c * l⁻¹ ∈ S.ctx.U₂ :=
  S.conj_mem_U₂ (Subgroup.le_normalizer (lv_le_L L v hl)) (S.ctx.hyp.norm₁ (lv_le_L L v hl))
    (lv_le_centralizer L v hl) hc

theorem T₁_conj_mem_U₂ {t c : G} (ht : t ∈ T ⊓ Subgroup.normalizer (V₁ : Set G))
    (hc : c ∈ S.ctx.U₂) : t * c * t⁻¹ ∈ S.ctx.U₂ :=
  S.conj_mem_U₂ (S.ctx.T₁_le_NL ht) ht.2 (S.ctx.T₁_le ht) hc

noncomputable def rv : ↥(lv L v) →* ↥(VecStab.vecStab (S.C₁.E v)) :=
  (S.C₁.ρ.comp (Subgroup.inclusion (lv_le_L L v))).codRestrict _ fun l =>
    (S.mem_centralizer_iff _).mp (lv_le_centralizer L v l.2)

theorem rv_surjective : Function.Surjective S.rv := by
  rintro ⟨g, hg⟩
  obtain ⟨l, hl, hlg⟩ := S.exists_mem_lv hg
  exact ⟨⟨l, hl⟩, Subtype.ext hlg⟩

theorem exists_levi : ∃ f : ↥(lv L v) →* SpecialLinearGroup (Fin (n - 1)) (ZMod 2),
    Function.Surjective f ∧ IsPGroup 2 f.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, hψ, hψk⟩ := VecStab.exists_levi S.one_add S.x₀_ne
  obtain ⟨ι⟩ := S.ctx.hyp.iso
  have hkerρ : S.C₁.ρ.ker = CFSG.pCore 2 ↥L := S.C₁.ker_eq S.three_le' ι
  refine ⟨ψ.comp S.rv, hψ.comp S.rv_surjective, fun x => ?_⟩
  have hx : S.rv (x : ↥(lv L v)) ∈ ψ.ker := x.2
  obtain ⟨j, hj⟩ := hψk ⟨_, hx⟩
  have hj' : S.rv ((x : ↥(lv L v)) ^ 2 ^ j) = 1 := by
    rw [map_pow]
    simpa using congrArg Subtype.val hj
  have hmem : Subgroup.inclusion (lv_le_L L v) ((x : ↥(lv L v)) ^ 2 ^ j) ∈ S.C₁.ρ.ker := by
    rw [MonoidHom.mem_ker]
    simpa [rv] using congrArg Subtype.val hj'
  rw [hkerρ] at hmem
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hmem⟩
  refine ⟨j + k, Subtype.ext (Subtype.ext ?_)⟩
  have h1 := congrArg (fun y : ↥(CFSG.pCore 2 ↥L) => ((y : ↥L) : G)) hk
  simp only [SubmonoidClass.coe_pow, Subgroup.coe_inclusion, OneMemClass.coe_one] at h1
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  rw [pow_add, pow_mul, h1]

theorem mem_lFamily : lv L v ∈ lFamily (T ⊓ Subgroup.normalizer (V₁ : Set G)) := by
  show lv L v ∈ cComp (lv L v ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G)))
  obtain ⟨f, hf, hfk⟩ := S.exists_levi
  have : IsSimpleGroup (SpecialLinearGroup (Fin (n - 1)) (ZMod 2)) :=
    Vol2Native.A312L.sl_isSimple_of_card_two (Nat.card_zmod 2) S.three_le
  refine mem_cComp_of_hom (lv_perfect L v) ?_ S.T₁_le_normalizer_lv f hf hfk
  intro h
  apply S.ctx.ne_bot_V₁
  rw [eq_bot_iff, ← h]
  exact S.V₁_le_lv

theorem exists_orderOf_seven : ∃ y ∈ lv L v, orderOf y = 7 := by
  obtain ⟨f, hf, -⟩ := S.exists_levi
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h7 : 7 ∣ Nat.card ↥(lv L v) := by
    have h1 := Subgroup.index_ker f
    rw [MonoidHom.range_eq_top.mpr hf, Subgroup.card_top] at h1
    refine (VecStab.seven_dvd_card (m := n - 1) (by rcases S.rank with h | h <;> omega)).trans ?_
    rw [← h1]
    exact Subgroup.index_dvd_card f.ker
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 7 h7
  exact ⟨y, y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩

end Setting

end Sec1216Lv

end CFSG.Quasithin.H13
