module

public import CFSG.Quasithin.EmptyFaithful.S151V3
public import CFSG.Quasithin.EmptyFaithful.S151U2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def s151uK (L : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ L ∧ ∀ u ∈ blockU L, x * u * x⁻¹ * u⁻¹ ∈ blockZ L}
  one_mem' := ⟨L.one_mem, fun u _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxL, hx⟩ ⟨hyL, hy⟩
    refine ⟨L.mul_mem hxL hyL, fun u hu => ?_⟩
    have hz := hy u hu
    have e : x * y * u * (x * y)⁻¹ * u⁻¹ =
        (x * (y * u * y⁻¹ * u⁻¹) * x⁻¹) * (x * u * x⁻¹ * u⁻¹) := by group
    rw [e, s151v_blockZ_comm hz hxL]
    exact (blockZ L).mul_mem hz (hx u hu)
  inv_mem' := by
    rintro x ⟨hxL, hx⟩
    refine ⟨L.inv_mem hxL, fun u hu => ?_⟩
    have hz := hx u hu
    have hc : x⁻¹ * (x * u * x⁻¹ * u⁻¹) * x⁻¹⁻¹ = (x * u * x⁻¹ * u⁻¹) :=
      s151v_blockZ_comm hz (L.inv_mem hxL)
    have e : x⁻¹ * u * x⁻¹⁻¹ * u⁻¹ = (x⁻¹ * (x * u * x⁻¹ * u⁻¹) * x⁻¹⁻¹)⁻¹ := by group
    rw [e, hc]
    exact (blockZ L).inv_mem hz

theorem s151uK_le (L : Subgroup G) : s151uK L ≤ L := fun _ hx => hx.1

theorem s151uK_conj {L : Subgroup G} {l x : G} (hl : l ∈ L) (hx : x ∈ s151uK L) :
    l * x * l⁻¹ ∈ s151uK L := by
  obtain ⟨hxL, hx⟩ := hx
  refine ⟨L.mul_mem (L.mul_mem hl hxL) (L.inv_mem hl), fun u hu => ?_⟩
  have hu' : l⁻¹ * u * l ∈ blockU L := by
    have := (Subgroup.mem_normalizer_iff.mp (s151v_L_le_normalizer_blockU L (L.inv_mem hl)) u).mp hu
    simpa using this
  have hz := hx _ hu'
  have e : l * x * l⁻¹ * u * (l * x * l⁻¹)⁻¹ * u⁻¹ =
      l * (x * (l⁻¹ * u * l) * x⁻¹ * (l⁻¹ * u * l)⁻¹) * l⁻¹ := by group
  rw [e, s151v_blockZ_comm hz hl]
  exact hz

theorem blockQ_le_K {L : Subgroup G} (hsh : IsShort2 L) : blockQ L ≤ s151uK L := fun q hq =>
  ⟨blockQ_le_L L hq, fun u hu => by
    have := blockQ_comm_blockU hsh q hq u hu
    have e : q * u * q⁻¹ * u⁻¹ = 1 := by rw [this]; group
    rw [e]; exact (blockZ L).one_mem⟩

theorem s151u_mk_eq_one_iff {L : Subgroup G} {x : ↥L} :
    (x : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 ↔ (x : G) ∈ pCoreOf 2 L := by
  rw [QuotientGroup.eq_one_iff, pCoreOf]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]

theorem s151uK_comm_mem {L : Subgroup G} (hsh : IsShort2 L)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hnt : ∃ l ∈ L, ∃ u ∈ blockU L, l * u * l⁻¹ * u⁻¹ ∉ blockZ L) :
    ∀ x ∈ s151uK L, ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ blockQ L := by
  have hKn : ((s151uK L).subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (s151uK_le L)]
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact s151uK_conj hl hx
    · intro hx
      have := s151uK_conj (L.inv_mem hl) hx
      simpa [mul_assoc] using this
  have hN := hKn.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (QuotientGroup.mk'_surjective _)
  rcases @CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple _ _ hq
      (((s151uK L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) hN with hcen | htop
  · intro x hx l hl
    have hxL : x ∈ L := hx.1
    have hxc : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hxL⟩ ∈
        Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) :=
      hcen ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have h := Subgroup.mem_center_iff.mp hxc (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨l, hl⟩)
    have h1 : ((⟨x, hxL⟩ * ⟨l, hl⟩ * ⟨x, hxL⟩⁻¹ * ⟨l, hl⟩⁻¹ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have h' : ((⟨x, hxL⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) * ((⟨l, hl⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) =
          ((⟨l, hl⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) * ((⟨x, hxL⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) := h.symm
      rw [h']
      group
    have h3 := s151u_mk_eq_one_iff.mp h1
    have h2 : ((⟨x, hxL⟩ * ⟨l, hl⟩ * ⟨x, hxL⟩⁻¹ * ⟨l, hl⟩⁻¹ : ↥L) : G) = x * l * x⁻¹ * l⁻¹ := rfl
    rw [h2] at h3
    exact h3
  · exfalso
    have hallK : ∀ x ∈ L, x ∈ s151uK L := by
      intro x hx
      have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hx⟩ ∈
          ((s151uK L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨k, hk, hkx⟩ := hmem
      have h1 : ((k⁻¹ * ⟨x, hx⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        have : (k : ↥L ⧸ CFSG.pCore 2 ↥L) = ((⟨x, hx⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) := hkx
        rw [this, inv_mul_cancel]
      have hq' : ((k⁻¹ * ⟨x, hx⟩ : ↥L) : G) ∈ pCoreOf 2 L := s151u_mk_eq_one_iff.mp h1
      have hkK : (k : G) ∈ s151uK L := Subgroup.mem_subgroupOf.mp hk
      have e : x = (k : G) * ((k⁻¹ * ⟨x, hx⟩ : ↥L) : G) := by simp
      rw [e]
      exact (s151uK L).mul_mem hkK (blockQ_le_K hsh hq')
    obtain ⟨l, hl, u, hu, hne⟩ := hnt
    exact hne ((hallK l hl).2 u hu)

theorem s151u_alg_aux {a s u u' z₁ z₂ : G} (e1 : a * u * a⁻¹ = s * (a * u' * a⁻¹) * s⁻¹)
    (hz₂ : a * u * a⁻¹ = z₂ * u) (hz₁ : a * u' * a⁻¹ = z₁ * u') (hc : s * z₁ * s⁻¹ = z₁) :
    s * u' * s⁻¹ * u⁻¹ = z₁⁻¹ * z₂ := by
  have h : z₂ * u = z₁ * (s * u' * s⁻¹) := by
    calc z₂ * u = a * u * a⁻¹ := hz₂.symm
      _ = s * (a * u' * a⁻¹) * s⁻¹ := e1
      _ = s * (z₁ * u') * s⁻¹ := by rw [hz₁]
      _ = (s * z₁ * s⁻¹) * (s * u' * s⁻¹) := by group
      _ = z₁ * (s * u' * s⁻¹) := by rw [hc]
  calc s * u' * s⁻¹ * u⁻¹ = z₁⁻¹ * (z₁ * (s * u' * s⁻¹)) * u⁻¹ := by group
    _ = z₁⁻¹ * (z₂ * u) * u⁻¹ := by rw [h]
    _ = z₁⁻¹ * z₂ := by group

theorem s151u_delta_mem_K {L : Subgroup G} {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G))
    (hc1 : ∀ u ∈ blockU L, a * u * a⁻¹ * u⁻¹ ∈ blockZ L) {l : G} (hl : l ∈ L) :
    a * l * a⁻¹ * l⁻¹ ∈ s151uK L := by
  have hsL : a * l * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp ha l).mp hl
  refine ⟨L.mul_mem hsL (L.inv_mem hl), fun u hu => ?_⟩
  have hu' : l⁻¹ * u * l ∈ blockU L := by
    have := (Subgroup.mem_normalizer_iff.mp (s151v_L_le_normalizer_blockU L (L.inv_mem hl)) u).mp hu
    simpa using this
  have hz1 := hc1 _ hu'
  have hz2 := hc1 u hu
  have key := s151u_alg_aux (a := a) (s := a * l * a⁻¹) (u := u) (u' := l⁻¹ * u * l)
    (z₁ := a * (l⁻¹ * u * l) * a⁻¹ * (l⁻¹ * u * l)⁻¹) (z₂ := a * u * a⁻¹ * u⁻¹) (by group)
    (by group) (by group) (s151v_blockZ_comm hz1 hsL)
  have e : a * l * a⁻¹ * l⁻¹ * u * (a * l * a⁻¹ * l⁻¹)⁻¹ * u⁻¹ =
      (a * l * a⁻¹) * (l⁻¹ * u * l) * (a * l * a⁻¹)⁻¹ * u⁻¹ := by group
  rw [e, key]
  exact (blockZ L).mul_mem ((blockZ L).inv_mem hz1) hz2

theorem s151u_block_inner [Finite G] {L B : Subgroup G} {a : G}
    (hsh : IsShort2 L) (hperf : ⁅L, L⁆ = L)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hnt : ∃ l ∈ L, ∃ u ∈ blockU L, l * u * l⁻¹ * u⁻¹ ∉ blockZ L)
    (hB : IsSylowTwoOf B L) (ha : a ∈ Subgroup.normalizer (L : Set G))
    (hacent : ∀ s ∈ B, a * s * a⁻¹ * s⁻¹ ∈ Subgroup.centralizer (L : Set G)) :
    ∃ u ∈ blockU L, (∀ l ∈ L, a * l * a⁻¹ = u * l * u⁻¹) ∧
      ∀ s ∈ B, s * u * s⁻¹ * u⁻¹ ∈ blockZ L := by
  have hQL : blockQ L ≤ L := blockQ_le_L L
  have hQB : blockQ L ≤ B := CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hB
  have hUQ : blockU L ≤ blockQ L := s151v_blockU_le_blockQ hsh
  have hUL : blockU L ≤ L := s151v_blockU_le_L hsh
  have hBL : B ≤ L := hB.1
  have haU : a ∈ Subgroup.normalizer (blockU L : Set G) := s151v_normalizer_le_normalizer_blockU L ha
  have hLQ : ∀ l ∈ L, ∀ t ∈ blockQ L, l * t * l⁻¹ ∈ blockQ L := fun l hl t ht =>
    (Subgroup.mem_normalizer_iff.mp (L_le_normalizer_blockQ L hl) t).mp ht
  have hLU : ∀ l ∈ L, ∀ t ∈ blockU L, l * t * l⁻¹ ∈ blockU L := fun l hl t ht =>
    (Subgroup.mem_normalizer_iff.mp (s151v_L_le_normalizer_blockU L hl) t).mp ht
  have hZc : ∀ z ∈ blockZ L, ∀ l ∈ L, l * z * l⁻¹ = z := fun z hz l hl => s151v_blockZ_comm hz hl
  have hZU : blockZ L ≤ blockU L := s151v_blockZ_le_blockU L
  have hc1 : ∀ u ∈ blockU L, a * u * a⁻¹ * u⁻¹ ∈ blockZ L := by
    intro u hu
    refine ⟨(blockU L).mul_mem ((Subgroup.mem_normalizer_iff.mp haU u).mp hu) ((blockU L).inv_mem hu), ?_⟩
    exact hacent u (hQB (hUQ hu))
  let δ : G → G := fun l => a * l * a⁻¹ * l⁻¹
  have hδL : ∀ l ∈ L, δ l ∈ L := fun l hl =>
    L.mul_mem ((Subgroup.mem_normalizer_iff.mp ha l).mp hl) (L.inv_mem hl)
  have hδK : ∀ l ∈ L, δ l ∈ s151uK L := fun l hl => s151u_delta_mem_K ha hc1 hl
  have hKc := s151uK_comm_mem hsh hq hnt
  have hcoc : ∀ x ∈ L, ∀ y ∈ L, δ (x * y) = δ x * (x * δ y * x⁻¹) := fun x _ y _ => by
    simp only [δ]; group
  have hδQ : ∀ l ∈ L, δ l ∈ blockQ L := by
    refine s151u_perf_map_mem hperf hLQ δ hδL (fun l hl m hm => ?_) (fun l hl m hm => ?_)
    · rw [hcoc l hl m hm]
      have h1 : l * δ m * l⁻¹ * (δ m)⁻¹ ∈ blockQ L := by
        have := (blockQ L).inv_mem (hKc (δ m) (hδK m hm) l hl)
        have e : (δ m * l * (δ m)⁻¹ * l⁻¹)⁻¹ = l * δ m * l⁻¹ * (δ m)⁻¹ := by group
        rwa [e] at this
      have h2 := hLQ (δ l) (hδL l hl) _ h1
      have e : δ l * (l * δ m * l⁻¹) * (δ l * δ m)⁻¹ = δ l * (l * δ m * l⁻¹ * (δ m)⁻¹) * (δ l)⁻¹ := by
        group
      rw [e]
      exact h2
    · have := hKc (δ l) (hδK l hl) (δ m) (hδL m hm)
      have e : δ l * δ m * (δ m * δ l)⁻¹ = δ l * δ m * (δ l)⁻¹ * (δ m)⁻¹ := by group
      rw [e]
      exact this
  have hδU : ∀ l ∈ L, δ l ∈ blockU L := by
    refine s151u_perf_map_mem hperf hLU δ hδL (fun l hl m hm => ?_) (fun l hl m hm => ?_)
    · rw [hcoc l hl m hm]
      have h1 : l * δ m * l⁻¹ * (δ m)⁻¹ ∈ blockU L := by
        have := (blockU L).inv_mem (Subgroup.commutator_mem_commutator (hδQ m hm) hl)
        have e : ⁅δ m, l⁆⁻¹ = l * δ m * l⁻¹ * (δ m)⁻¹ := by
          simp only [commutatorElement_def]; group
        rwa [e] at this
      have h2 := hLU (δ l) (hδL l hl) _ h1
      have e : δ l * (l * δ m * l⁻¹) * (δ l * δ m)⁻¹ = δ l * (l * δ m * l⁻¹ * (δ m)⁻¹) * (δ l)⁻¹ := by
        group
      rw [e]
      exact h2
    · have e : δ l * δ m * (δ m * δ l)⁻¹ = ⁅δ l, δ m⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.commutator_mem_commutator (hδQ l hl) (hδL m hm)
  have hδB : ∀ p ∈ B, δ p ∈ blockZ L := fun p hp =>
    ⟨hδU p (hBL hp), hacent p hp⟩
  have hUab : ∀ a ∈ blockU L, ∀ b ∈ blockU L, a * b = b * a := s151v_blockU_comm hsh
  have hU2 : ∀ a ∈ blockU L, a * a = 1 := fun a ha => by
    have := s151v_blockU_sq hsh a ha
    rwa [sq] at this
  obtain ⟨u, hu, hall⟩ := s151u_transfer (L := L) (P := B) (U := blockU L) (Z := blockZ L) (δ := δ)
    hB.2.2 hUab hU2 hLU hZc hδU hcoc hδB
  refine ⟨u, hu, ?_, ?_⟩
  ·
    let ε : G → G := fun x => x⁻¹ * u⁻¹ * (a * x * a⁻¹) * u
    have hεZ : ∀ x ∈ L, ε x ∈ blockZ L := by
      intro x hx
      obtain ⟨ζ, hζ, hδx⟩ := hall x hx
      have e1 : a * x * a⁻¹ = (u * (x * u * x⁻¹)⁻¹ * ζ) * x := by
        have : δ x * x = a * x * a⁻¹ := by simp only [δ]; group
        rw [← this, hδx]
      have e2 : ε x = (x * u)⁻¹ * ζ * (x * u) := by
        simp only [ε]
        rw [e1]
        group
      have e3 := hZc ζ hζ (x * u)⁻¹ (L.inv_mem (L.mul_mem hx (hUL hu)))
      rw [inv_inv] at e3
      rw [e2, e3]
      exact hζ
    have hεL : ∀ x ∈ L, ε x ∈ L := fun x hx =>
      L.mul_mem (L.mul_mem (L.mul_mem (L.inv_mem hx) (L.inv_mem (hUL hu)))
        ((Subgroup.mem_normalizer_iff.mp ha x).mp hx)) (hUL hu)
    have hε := s151u_perf_map_mem (L := L) (T := ⊥) hperf (fun l _ t ht => by
        rw [Subgroup.mem_bot] at ht ⊢
        rw [ht]; group) ε hεL (fun x hx y hy => by
        rw [Subgroup.mem_bot]
        have hc : y⁻¹ * ε x * y = ε x := by
          have := hZc (ε x) (hεZ x hx) y⁻¹ (L.inv_mem hy)
          rwa [inv_inv] at this
        have e : ε (x * y) = y⁻¹ * ε x * y * ε y := by simp only [ε]; group
        rw [e, hc]
        group) (fun x hx y hy => by
        rw [Subgroup.mem_bot]
        have hc : ε x * ε y * (ε x)⁻¹ = ε y := hZc (ε y) (hεZ y hy) (ε x) (hεL x hx)
        have h : ε x * ε y = ε y * ε x := by
          calc ε x * ε y = (ε x * ε y * (ε x)⁻¹) * ε x := by group
            _ = ε y * ε x := by rw [hc]
        rw [h]
        group)
    intro l hl
    have h1 : ε l = 1 := Subgroup.mem_bot.mp (hε l hl)
    calc a * l * a⁻¹ = u * (l * ε l) * u⁻¹ := by simp only [ε]; group
      _ = u * l * u⁻¹ := by rw [h1, mul_one]
  · intro s hs
    obtain ⟨ζ, hζ, hδs⟩ := hall s (hBL hs)
    have h1 : u * (s * u * s⁻¹)⁻¹ ∈ blockZ L := by
      have e : u * (s * u * s⁻¹)⁻¹ = δ s * ζ⁻¹ := by rw [hδs]; group
      rw [e]
      exact (blockZ L).mul_mem (hδB s hs) ((blockZ L).inv_mem hζ)
    have h2 := (blockZ L).inv_mem h1
    have e : (u * (s * u * s⁻¹)⁻¹)⁻¹ = s * u * s⁻¹ * u⁻¹ := by group
    rwa [e] at h2

theorem s151u_fixed_by_L {L : Subgroup G} (hsh : IsShort2 L) {u₁ : G} (hu₁ : u₁ ∈ blockU L)
    (hu₁Z : u₁ ∉ blockZ L) (hfix : ∀ l ∈ L, l * u₁ * l⁻¹ * u₁⁻¹ ∈ blockZ L) :
    ∀ u₂ ∈ blockU L, u₂ ∈ blockZ L ∨ u₁⁻¹ * u₂ ∈ blockZ L := by
  have hZc : ∀ z ∈ blockZ L, ∀ l ∈ L, l * z * l⁻¹ = z := fun z hz l hl => s151v_blockZ_comm hz hl
  have hZc' : ∀ z ∈ blockZ L, ∀ l ∈ L, l * z = z * l := fun z hz l hl => by
    have := hZc z hz l hl
    calc l * z = (l * z * l⁻¹) * l := by group
      _ = z * l := by rw [this]
  have hu₁L : u₁ ∈ L := s151v_blockU_le_L hsh hu₁
  have hu₁2 : u₁ * u₁ = 1 := by
    have := s151v_blockU_sq hsh u₁ hu₁
    rwa [sq] at this
  have hu₁i2 : u₁⁻¹ * u₁⁻¹ = 1 := by
    calc u₁⁻¹ * u₁⁻¹ = (u₁ * u₁)⁻¹ := by group
      _ = 1 := by rw [hu₁2]; simp
  let W : Subgroup G :=
    { carrier := {w | w ∈ blockZ L ∨ u₁⁻¹ * w ∈ blockZ L}
      one_mem' := Or.inl (blockZ L).one_mem
      mul_mem' := by
        rintro w₁ w₂ (h₁ | h₁) (h₂ | h₂)
        · exact Or.inl ((blockZ L).mul_mem h₁ h₂)
        · right
          have e : u₁⁻¹ * (w₁ * w₂) = w₁ * (u₁⁻¹ * w₂) := by
            have := hZc' w₁ h₁ u₁⁻¹ (L.inv_mem hu₁L)
            calc u₁⁻¹ * (w₁ * w₂) = (u₁⁻¹ * w₁) * w₂ := by group
              _ = (w₁ * u₁⁻¹) * w₂ := by rw [this]
              _ = w₁ * (u₁⁻¹ * w₂) := by group
          rw [e]
          exact (blockZ L).mul_mem h₁ h₂
        · right
          have e : u₁⁻¹ * (w₁ * w₂) = (u₁⁻¹ * w₁) * w₂ := by group
          rw [e]
          exact (blockZ L).mul_mem h₁ h₂
        · left
          have e : w₁ * w₂ = (u₁⁻¹ * w₁) * (u₁⁻¹ * w₂) := by
            have hc := hZc' (u₁⁻¹ * w₁) h₁ u₁ hu₁L
            calc w₁ * w₂ = (u₁ * (u₁⁻¹ * w₁)) * (u₁ * (u₁⁻¹ * w₂)) := by group
              _ = u₁ * ((u₁⁻¹ * w₁) * u₁) * (u₁⁻¹ * w₂) := by group
              _ = u₁ * (u₁ * (u₁⁻¹ * w₁)) * (u₁⁻¹ * w₂) := by rw [← hc]
              _ = (u₁ * u₁) * (u₁⁻¹ * w₁) * (u₁⁻¹ * w₂) := by group
              _ = (u₁⁻¹ * w₁) * (u₁⁻¹ * w₂) := by rw [hu₁2, one_mul]
          rw [e]
          exact (blockZ L).mul_mem h₁ h₂
      inv_mem' := by
        rintro w (h | h)
        · exact Or.inl ((blockZ L).inv_mem h)
        · right
          have hc := hZc' (u₁⁻¹ * w)⁻¹ ((blockZ L).inv_mem h) u₁⁻¹ (L.inv_mem hu₁L)
          have e : u₁⁻¹ * w⁻¹ = (u₁⁻¹ * w)⁻¹ := by
            calc u₁⁻¹ * w⁻¹ = (u₁⁻¹ * (u₁⁻¹ * w)⁻¹) * u₁⁻¹ := by group
              _ = ((u₁⁻¹ * w)⁻¹ * u₁⁻¹) * u₁⁻¹ := by rw [hc]
              _ = (u₁⁻¹ * w)⁻¹ * (u₁⁻¹ * u₁⁻¹) := by group
              _ = (u₁⁻¹ * w)⁻¹ := by rw [hu₁i2, mul_one]
          rw [e]
          exact (blockZ L).inv_mem h }
  have hZW : blockZ L ≤ W := fun z hz => Or.inl hz
  have hWU : W ≤ blockU L := by
    intro w hw
    rcases hw with h | h
    · exact s151v_blockZ_le_blockU L h
    · have e : w = u₁ * (u₁⁻¹ * w) := by group
      rw [e]
      exact (blockU L).mul_mem hu₁ (s151v_blockZ_le_blockU L h)
  have hWc : ∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W := by
    intro l hl w hw
    rcases hw with h | h
    · left
      rw [hZc w h l hl]
      exact h
    · right
      have hz' := hfix l hl
      have hz : l * (u₁⁻¹ * w) * l⁻¹ = u₁⁻¹ * w := hZc _ h l hl
      have e : u₁⁻¹ * (l * w * l⁻¹) =
          (u₁⁻¹ * (l * u₁ * l⁻¹)) * (l * (u₁⁻¹ * w) * l⁻¹) := by group
      have e2 : u₁⁻¹ * (l * u₁ * l⁻¹) = l * u₁ * l⁻¹ * u₁⁻¹ := by
        have := hZc _ hz' u₁⁻¹ (L.inv_mem hu₁L)
        rw [inv_inv] at this
        calc u₁⁻¹ * (l * u₁ * l⁻¹) = u₁⁻¹ * (l * u₁ * l⁻¹ * u₁⁻¹) * u₁ := by group
          _ = l * u₁ * l⁻¹ * u₁⁻¹ := this
      rw [e, hz, e2]
      exact (blockZ L).mul_mem hz' h
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact fun hw => hWc l hl w hw
    · intro h
      have := hWc l⁻¹ (L.inv_mem hl) _ h
      simpa [mul_assoc] using this
  intro u₂ hu₂
  rcases hsh.2.2.2.2.2 W hZW hWU hLW with h | h
  · exfalso
    apply hu₁Z
    have hmem : u₁ ∈ W := Or.inr (by simp)
    rw [h] at hmem
    exact hmem
  · have hmem : u₂ ∈ W := by rw [h]; exact hu₂
    exact hmem

theorem s151u_nontrivial_action {L : Subgroup G} (hsh : IsShort2 L)
    (hrank : ∃ u₁ ∈ blockU L, ∃ u₂ ∈ blockU L, u₁ ∉ blockZ L ∧ u₂ ∉ blockZ L ∧
      u₁⁻¹ * u₂ ∉ blockZ L) :
    ∃ l ∈ L, ∃ u ∈ blockU L, l * u * l⁻¹ * u⁻¹ ∉ blockZ L := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u₁, hu₁, u₂, hu₂, hu₁Z, hu₂Z, hu₁₂Z⟩ := hrank
  rcases s151u_fixed_by_L hsh hu₁ hu₁Z (fun l hl => hcon l hl u₁ hu₁) u₂ hu₂ with h | h
  · exact hu₂Z h
  · exact hu₁₂Z h

end CFSG.Quasithin
