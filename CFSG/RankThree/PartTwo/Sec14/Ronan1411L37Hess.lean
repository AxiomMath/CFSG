module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1411L37Bridge
public import CFSG.RankThree.PartTwo.Sec14.Wales1411WL3Tori
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJInner
import CFSG.RankThree.PartTwo.Sec14.Wales1411WTori
import CFSG.LargeExtraspecial.S8DimB

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1411L37

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

section Transport

private theorem map_pCoreOf {G G' : Type*} [Group G] [Group G'] (p : ℕ) (f : G →* G')
    (hf : Function.Injective f) (K : Subgroup G) :
    (CFSG.Open.pCoreOf p K).map f = CFSG.Open.pCoreOf p (K.map f) := by
  unfold CFSG.Open.pCoreOf
  rw [← CFSG.pCore_map_iso p (K.equivMapOfInjective f hf), Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem normalizer_le_normalizer_pCoreOf {G : Type} [Group G] [Finite G] (p : ℕ)
    (H : Subgroup G) : Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf p H : Set G) := by
  intro g hg
  refine Wales1411W.mem_normalizer_of_map_conj_le ?_
  rw [map_pCoreOf p _ (MulAut.conj g).injective, Wales1411W.map_conj_eq_self hg]

variable {M : Type} [Group M] {X : Subgroup M}

private theorem map_centralizer_subtype (x : ↥X) :
    (Subgroup.centralizer ({x} : Set ↥X)).map X.subtype =
      X ⊓ Subgroup.centralizer ({(x : M)} : Set M) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, congrArg Subtype.val hz⟩
  · rintro ⟨hyX, hy⟩
    exact ⟨⟨y, hyX⟩, Subtype.ext hy, rfl⟩

private theorem mem_normalizer_map {W : Subgroup ↥X} {n : ↥X}
    (hn : n ∈ Subgroup.normalizer (W : Set ↥X)) :
    (n : M) ∈ Subgroup.normalizer ((W.map X.subtype : Subgroup M) : Set M) := by
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro m
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨n * w * n⁻¹, (hn w).mp hw, rfl⟩
  · rintro ⟨w, hw, hwm⟩
    rw [Subgroup.coe_subtype] at hwm
    have hmX : m ∈ X := by
      have : m = (n : M)⁻¹ * (w : M) * n := by
        rw [hwm]
        group
      rw [this]
      exact mul_mem (mul_mem (inv_mem n.2) w.2) n.2
    refine ⟨⟨m, hmX⟩, (hn ⟨m, hmX⟩).mpr ?_, rfl⟩
    have : n * ⟨m, hmX⟩ * n⁻¹ = w := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hwm.symm)
    rw [this]
    exact hw

private theorem mem_normalizer_of_map {W : Subgroup ↥X} {n : ↥X}
    (hn : (n : M) ∈ Subgroup.normalizer ((W.map X.subtype : Subgroup M) : Set M)) :
    n ∈ Subgroup.normalizer (W : Set ↥X) := by
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro w
  have h := hn (w : M)
  constructor
  · intro hw
    obtain ⟨w', hw', hww'⟩ := h.mp ⟨w, hw, rfl⟩
    have : w' = n * w * n⁻¹ := Subtype.ext (by simpa using hww')
    rw [← this]
    exact hw'
  · intro hw
    obtain ⟨w', hw', hww'⟩ := h.mpr ⟨n * w * n⁻¹, hw, rfl⟩
    have : w' = w := Subtype.ext hww'
    rw [← this]
    exact hw'

private theorem mem_normalizer_inf_centralizer [hX : X.Normal] {e m : M} (hme : m * e = e * m) :
    m ∈ Subgroup.normalizer ((X ⊓ Subgroup.centralizer {e} : Subgroup M) : Set M) := by
  have hc : Commute m e := hme
  rw [Subgroup.mem_normalizer_iff]
  intro z
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hzX, hze⟩
    exact ⟨hX.conj_mem z hzX m, ((hc.mul_left hze).mul_left hc.inv_left).eq⟩
  · rintro ⟨hzX, hze⟩
    have hz : m⁻¹ * (m * z * m⁻¹) * m = z := by group
    refine ⟨?_, ?_⟩
    · have h2 := hX.conj_mem _ hzX m⁻¹
      rwa [inv_inv, hz] at h2
    · have h1 : Commute (m⁻¹ * (m * z * m⁻¹) * m) e := (hc.inv_left.mul_left hze).mul_left hc
      rw [hz] at h1
      exact h1.eq

private theorem conj_injective_of_center {G : Type*} [Group G] (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
  intro g hg
  rw [Subgroup.mem_center_iff]
  intro h
  have h1 : MulAut.conj g h = h := by rw [MonoidHom.mem_ker.mp hg]; rfl
  rw [MulAut.conj_apply] at h1
  calc h * g = g * h * g⁻¹ * g := by rw [h1]
    _ = g * h := by group

end Transport

section Hess

variable {M : Type} [Group M] [Finite M] {Ybar Abar Xbar Rbar : Subgroup M} {abar : M}

theorem etrans2_of_hess (hTori : KL3HessTori) [hXn : Xbar.Normal] {p f : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hiso : Sec4.IsoLThreePi ↥Xbar p f) {E : Subgroup M}
    (hEX : E ≤ Xbar) (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (htr : ∀ x ∈ E, x ≠ 1 → ∀ y ∈ E, y ≠ 1 →
      ∃ n ∈ Xbar ⊓ Subgroup.normalizer (E : Set M), n * x * n⁻¹ = y) :
    Wales1411W.ETrans2 M E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E' : Subgroup ↥Xbar := E.subgroupOf Xbar with hE'
  have hE'map : E'.map Xbar.subtype = E := Subgroup.map_subgroupOf_eq_of_le hEX
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE'e : CFSG.Assembly.IsElemAbelian 3 E' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      show ((a : ↥Xbar) : M) * ((b : ↥Xbar) : M) = ((b : ↥Xbar) : M) * ((a : ↥Xbar) : M)
      exact hcommE _ a.2 _ b.2
    · apply Subtype.ext
      show (x : M) ^ 3 = 1
      exact hEe.2 _ hx
  have hE'9 : Nat.card E' = 9 := by
    rw [hE', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv, hE9]
  have hE'tr : ∀ y₀ ∈ E', y₀ ≠ 1 → ∀ y₁ ∈ E', y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E' : Set ↥Xbar), w * y₀ * w⁻¹ = y₁ := by
    intro y₀ hy₀ hy₀1 y₁ hy₁ hy₁1
    obtain ⟨n, hn, hny⟩ := htr (y₀ : M) hy₀ (fun h => hy₀1 (Subtype.ext h)) (y₁ : M) hy₁
      (fun h => hy₁1 (Subtype.ext h))
    obtain ⟨hnX, hnE⟩ := Subgroup.mem_inf.mp hn
    refine ⟨⟨n, hnX⟩, mem_normalizer_of_map ?_, Subtype.ext hny⟩
    rw [hE'map]
    exact hnE
  obtain ⟨hT1, hT2⟩ := hTori ↥Xbar p f hp2 hf hiso E' hE'e hE'9 hE'tr
  set U : M → Subgroup M := fun e => CFSG.Open.pCoreOf 2 (Xbar ⊓ Subgroup.centralizer {e})
    with hU
  have hUmap : ∀ x : ↥Xbar, (CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({x} : Set ↥Xbar))).map
      Xbar.subtype = U x := fun x => by
    rw [map_pCoreOf 2 _ Xbar.subtype_injective, map_centralizer_subtype]
  have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hEe.2 x x.2)⟩
  have hnormU : ∀ e : M, ∀ m : M, m * e = e * m →
      m ∈ Subgroup.normalizer (U e : Set M) := fun e m hme =>
    normalizer_le_normalizer_pCoreOf 2 _ (mem_normalizer_inf_centralizer hme)
  refine Wales1411W.etrans2_of_tori (N := Xbar) U hE3 ?_ ?_ ?_ ?_ ?_ ?_
  ·
    intro m ε hε
    rw [commutatorElement_def]
    exact mul_mem (hXn.conj_mem ε (hEX hε) m) (inv_mem (hEX hε))
  · intro e _
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  · intro e he ε hε
    exact hnormU e ε (hcommE ε hε e he)
  · intro e he m hm
    exact hnormU e m (Subgroup.mem_centralizer_iff.mp hm e he).symm
  ·
    intro W hWX hW2 hEW hW1
    set W' : Subgroup ↥Xbar := W.subgroupOf Xbar with hW'
    have hW'map : W'.map Xbar.subtype = W := Subgroup.map_subgroupOf_eq_of_le hWX
    have hW'2 : IsPGroup 2 W' := hW2.comap_subtype
    have hEW' : E' ≤ Subgroup.normalizer (W' : Set ↥Xbar) := by
      intro ε hε
      refine mem_normalizer_of_map ?_
      rw [hW'map]
      exact hEW hε
    have hW'1 : W' ≠ ⊥ := by
      intro h
      apply hW1
      rw [← hW'map, h, Subgroup.map_bot]
    obtain ⟨x, hx, hWx⟩ := hT1 W' hW'2 hEW' hW'1
    refine ⟨x, hx, ?_⟩
    rw [← hW'map, ← hUmap x]
    exact Subgroup.map_mono hWx
  ·
    intro e he e' he' W W' hW1 hW'1 hWU hW'U hEW hEW'
    have heX : e ∈ Xbar := hEX he
    have he'X : e' ∈ Xbar := hEX he'
    have hUeX : U e ≤ Xbar := by
      rw [← hUmap ⟨e, heX⟩]
      exact Subgroup.map_subtype_le _
    have hUe'X : U e' ≤ Xbar := by
      rw [← hUmap ⟨e', he'X⟩]
      exact Subgroup.map_subtype_le _
    set V : Subgroup ↥Xbar := W.subgroupOf Xbar with hV
    set V' : Subgroup ↥Xbar := W'.subgroupOf Xbar with hV'
    have hVmap : V.map Xbar.subtype = W := Subgroup.map_subgroupOf_eq_of_le (hWU.trans hUeX)
    have hV'map : V'.map Xbar.subtype = W' :=
      Subgroup.map_subgroupOf_eq_of_le (hW'U.trans hUe'X)
    have hV1 : V ≠ ⊥ := fun h => hW1 (by rw [← hVmap, h, Subgroup.map_bot])
    have hV'1 : V' ≠ ⊥ := fun h => hW'1 (by rw [← hV'map, h, Subgroup.map_bot])
    have hVU : V ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({⟨e, heX⟩} : Set ↥Xbar)) := by
      intro v hv
      have hv' : (v : M) ∈ U e := hWU hv
      rw [← hUmap ⟨e, heX⟩] at hv'
      obtain ⟨u, hu, huv⟩ := hv'
      rwa [Subtype.ext huv] at hu
    have hV'U : V' ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({⟨e', he'X⟩} : Set ↥Xbar)) := by
      intro v hv
      have hv' : (v : M) ∈ U e' := hW'U hv
      rw [← hUmap ⟨e', he'X⟩] at hv'
      obtain ⟨u, hu, huv⟩ := hv'
      rwa [Subtype.ext huv] at hu
    have hEV : E' ≤ Subgroup.normalizer (V : Set ↥Xbar) := by
      intro ε hε
      refine mem_normalizer_of_map ?_
      rw [hVmap]
      exact hEW hε
    have hEV' : E' ≤ Subgroup.normalizer (V' : Set ↥Xbar) := by
      intro ε hε
      refine mem_normalizer_of_map ?_
      rw [hV'map]
      exact hEW' hε
    obtain ⟨n, hn, hnU⟩ := hT2 ⟨e, heX⟩ he ⟨e', he'X⟩ he' V V' hV1 hV'1 hVU hV'U hEV hEV'
    obtain ⟨hnVV, hnE⟩ := Subgroup.mem_inf.mp hn
    refine ⟨n, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · have h := Subgroup.mem_map_of_mem Xbar.subtype hnVV
      rwa [Subgroup.map_sup, hVmap, hV'map] at h
    · have h := mem_normalizer_map hnE
      rwa [hE'map] at h
    · rw [← hUmap ⟨e, heX⟩, ← hUmap ⟨e', he'X⟩, ← hnU, Subgroup.map_map, Subgroup.map_map]
      congr 1

theorem conj_of_hess (hTori : KL3HessTori) (hset : HJCoreSetting Ybar Abar Xbar Rbar abar)
    (hX : ∃ _ : Fact (Nat.Prime 7),
      Nonempty (↥Xbar ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)))
    (hAX : Abar ⊔ Xbar = Subgroup.zpowers abar ⊔ Xbar)
    (htr : ∀ x ∈ Abar ⊓ Xbar, x ≠ 1 → ∀ y ∈ Abar ⊓ Xbar, y ≠ 1 →
      ∃ n ∈ Xbar ⊓ Subgroup.normalizer ((Abar ⊓ Xbar : Subgroup M) : Set M), n * x * n⁻¹ = y)
    {S T : Subgroup M} (hS : Maximal (Wales1411W.InvTwo Abar Ybar) S)
    (hT : Maximal (Wales1411W.InvTwo Abar Ybar) T) (hST : S ⊔ T = Ybar) :
    ∃ n ∈ Ybar ⊓ Subgroup.normalizer (Abar : Set M), T = S.map (MulAut.conj n).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h7, hiso, hs, -⟩ := exists_model hX
  haveI hXn := Wales1411W.HJInner.normal_X hset
  have hna : ∃ a b : ↥Xbar, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have htop : commutator ↥Xbar = ⊤ := @Group.IsPerfect.commutator_eq_top _ _ hset.perfect
    have hbot : commutator ↥Xbar = ⊥ := by
      rw [commutator_def, eq_bot_iff]
      refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.2 (h g₁ g₂)
    obtain ⟨g, hg⟩ := exists_ne (1 : ↥Xbar)
    have : g ∈ (⊥ : Subgroup ↥Xbar) := hbot ▸ htop ▸ Subgroup.mem_top g
    exact hg (Subgroup.mem_bot.1 this)
  obtain ⟨-, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna
  have hcen : Function.Injective (MulAut.conj : ↥Xbar →* MulAut ↥Xbar) :=
    conj_injective_of_center hZ
  have hAeq : Abar = Abar ⊓ Xbar ⊔ Subgroup.zpowers abar := by
    refine le_antisymm (fun e he => ?_) (sup_le inf_le_left
      (Subgroup.zpowers_le.mpr hset.mem_A))
    have heAX : e ∈ Subgroup.zpowers abar ⊔ Xbar := hAX ▸ Subgroup.mem_sup_left he
    obtain ⟨z, hz, x, hx, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp heAX
    have hzA : z ∈ Abar := Subgroup.zpowers_le.mpr hset.mem_A hz
    have hxA : x ∈ Abar := by
      have : x = z⁻¹ * (z * x) := by group
      rw [this]
      exact mul_mem (inv_mem hzA) he
    exact mul_mem (Subgroup.mem_sup_right hz) (Subgroup.mem_sup_left ⟨hxA, hx⟩)
  have hE9 : Nat.card (Abar ⊓ Xbar : Subgroup M) = 9 := by
    have hB : Subgroup.zpowers abar ≤
        Subgroup.normalizer ((Abar ⊓ Xbar : Subgroup M) : Set M) := by
      rw [Subgroup.zpowers_le]
      refine Late.le_normalizer_inf (Subgroup.le_normalizer : Abar ≤ _)
        (by rw [Subgroup.normalizer_eq_top (H := Xbar)]; exact le_top) hset.mem_A
    have h := CFSG.LargeExtraspecial.S8.card_sup_mul_card_inf_of_le_normalizer' hB
    rw [← hAeq, hset.card_A] at h
    have hbot : Abar ⊓ Xbar ⊓ Subgroup.zpowers abar = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have : z ∈ Subgroup.zpowers abar ⊓ Xbar := ⟨hz.2, hz.1.2⟩
      rwa [Wales1411W.HJInner.zpowers_inf_eq_bot hset hcen] at this
    rw [hbot, Subgroup.card_bot, mul_one, Nat.card_zpowers,
      orderOf_eq_prime (hset.isElemAbelian.2 abar hset.mem_A) hset.ne_one] at h
    omega
  have hEe : CFSG.Assembly.IsElemAbelian 3 (Abar ⊓ Xbar) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hset.isElemAbelian.2 x hx.1⟩
    show (a : M) * b = b * a
    exact congrArg Subtype.val (hset.isElemAbelian.1.is_comm.comm ⟨a, a.2.1⟩ ⟨b, b.2.1⟩)
  have hET := etrans2_of_hess hTori (p := 7) (f := 1) (by norm_num) le_rfl hiso inf_le_right hEe
    hE9 htr
  have hmax : ∀ R : Subgroup M, Maximal (Wales1411W.InvTwo Abar Ybar) R →
      Maximal (Wales1411W.InvTwo (Abar ⊓ Xbar) (S ⊔ T)) R := by
    intro R hR
    obtain ⟨hRY, hAR, hR2⟩ := hR.prop
    refine ⟨⟨hST ▸ hRY, inf_le_left.trans hAR, hR2⟩, fun U hU hRU => ?_⟩
    obtain ⟨hUY, hEU, hU2⟩ := hU
    rw [hST] at hUY
    exact hR.2 ⟨hUY, Wales1411W.HJInner.le_normalizer_of_inf hset hAeq hUY hEU, hU2⟩ hRU
  obtain ⟨n, hn, hnT⟩ := hET S T (hmax S hS) (hmax T hT)
  obtain ⟨hnY, hnE⟩ := Subgroup.mem_inf.mp hn
  rw [hST] at hnY
  refine ⟨n, Subgroup.mem_inf.mpr ⟨hnY, ?_⟩, hnT⟩
  have hna' : n * abar = abar * n :=
    Subgroup.mem_centralizer_singleton_iff.mp (hset.le_centralizer_a hnY)
  have hz : Subgroup.zpowers n ≤ Subgroup.normalizer ((Subgroup.zpowers abar : Subgroup M) :
      Set M) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hc : Commute n (abar ^ k) := Commute.zpow_right hna' k
    rw [hc.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers abar k
  have h := Wales1411W.le_normalizer_sup_of_le (Subgroup.zpowers_le.mpr hnE) hz
  rw [← hAeq] at h
  exact h (Subgroup.mem_zpowers n)

end Hess

end CFSG.RankThree.PartTwo.Sec14.Ronan1411L37
