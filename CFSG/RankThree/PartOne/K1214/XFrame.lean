module

public import CFSG.RankThree.PartOne.S12.Sec12FusSyl
import CFSG.RankThree.PartOne.S12.LinAlg
import CFSG.RankThree.PartOne.S12.Sec126a
import CFSG.RankThree.PartOne.S12.Sec12Three
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.RankThree.PartOne.K1214

open CFSG
open scoped commutatorElement

variable {G : Type} [Group G]

section Data

variable [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem pCoreFixed_eq_commutator_of_facts (hfacts : Sec12Facts G p A c L E)
    (h : Sec12Hyp G p A c L E) (hX : torusWeylHasPCore p E) :
    pCoreFixed p E = ⁅E, L ⊓ torusNormalizer E⁆ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card E :=
    dvd_trans (dvd_pow_self p (by norm_num)) h.pow_three_dvd_card_E
  have hinvW := torusInvariant_pCoreFixed p E
  have hinvL : torusInvariant E L (pCoreFixed p E) := fun w hw =>
    hinvW w ⟨Subgroup.mem_top w, hw.2⟩
  rcases hfacts.four.1 (pCoreFixed p E) (pCoreFixed_le p E) hinvL
      (pCoreFixed_ne_bot hdvd) (pCoreFixed_ne_top hX) with hc | hc
  · exact absurd (torusNormalizer_le_cNormalizer_of_invariant (hc ▸ hinvW)) hfacts.five
  · exact hc

theorem data_of_ctx (ctx : Fus12Ctx G p A c L E) :
    Sec1211.Data p (torusWeyl E).subtype ((E ⊓ L).subgroupOf E) (CFSG.pCore p ↥(torusWeyl E)) := by
  have h := ctx.hyp
  have hX := ctx.core
  have hfix := ctx.ten.1
  have hcard := ctx.ten.2.1
  have hZ := ctx.ten.2.2
  have hp := h.prime
  have hcL : c ∉ L := Sec12Three.c_not_mem_L h hZ
  have hBle : E ⊓ L ≤ E := inf_le_left
  have hmemB : ∀ b : ↥E, b ∈ (E ⊓ L).subgroupOf E ↔ (b : G) ∈ E ⊓ L := fun b =>
    Subgroup.mem_subgroupOf
  refine
    { prime := hp
      comm := fun a b => h.E_elem.is_comm.comm a b
      pow_eq_one := fun a => Subtype.ext (by simpa using Sec12Three.pow_eq_one_of_mem_E h a.2)
      card_eq := ?_
      α_inj := Subtype.val_injective
      X_normal := fun w x hx =>
        (CFSG.pCore_normal (p := p) (G := ↥(torusWeyl E))).conj_mem x hx w
      X_pgroup := CFSG.pCore_isPGroup
      X_fixes := ?_
      B_inv := ?_
      B_irr := ?_
      X_ne_bot := hX }
  · exact hcard.trans (congrArg (p * ·)
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBle).toEquiv.symm))
  · intro x hx b hb
    exact (mem_pCoreFixed.1 (hfix.ge ((hmemB b).1 hb))).2 x hx
  · intro w b hb
    have hinv := (LinAlg.torusInvariant_top_iff_forall_torusWeyl (pCoreFixed_le p E)).1
      (torusInvariant_pCoreFixed p E) (w : MulAut E) w.2 b (hfix.ge ((hmemB b).1 hb))
    exact (hmemB _).2 (hfix.le hinv)
  · intro S hS hSinv
    have hS'E : S.map E.subtype ≤ E := Subgroup.map_subtype_le S
    have hS'B : S.map E.subtype ≤ E ⊓ L := by
      intro x hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hx
      exact (hmemB s).1 (hS hs)
    have hinvW : torusInvariant E ⊤ (S.map E.subtype) := by
      rw [LinAlg.torusInvariant_top_iff_forall_torusWeyl hS'E]
      intro φ hφ b hb
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hb
      exact Subgroup.mem_map.2 ⟨(torusWeyl E).subtype ⟨φ, hφ⟩ s, hSinv ⟨φ, hφ⟩ s hs, rfl⟩
    have hinvL : torusInvariant E L (S.map E.subtype) := fun w hw =>
      hinvW w ⟨Subgroup.mem_top w, hw.2⟩
    by_cases hS0 : S.map E.subtype = ⊥
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective S E.subtype_injective).1 hS0
    · right
      have hS'ne : S.map E.subtype ≠ E := fun heq =>
        pCoreFixed_ne_top hX (le_antisymm (pCoreFixed_le p E)
          (heq.symm.le.trans (hS'B.trans hfix.ge)))
      rcases ctx.facts.four.1 _ hS'E hinvL hS0 hS'ne with hc | hc
      · exfalso
        have hcS : c ∈ S.map E.subtype := hc ▸ Subgroup.mem_zpowers c
        exact hcL (Subgroup.mem_inf.1 (hS'B hcS)).2
      · apply Subgroup.map_injective E.subtype_injective
        calc S.map E.subtype = ⁅E, L ⊓ torusNormalizer E⁆ := hc
          _ = pCoreFixed p E := (pCoreFixed_eq_commutator_of_facts ctx.facts h hX).symm
          _ = E ⊓ L := hfix
          _ = ((E ⊓ L).subgroupOf E).map E.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hBle).symm

theorem not_dvd_torusImage (ctx : Fus12Ctx G p A c L E) (hn12 : ¬ RowModel p L 12) :
    ¬ p ∣ Nat.card ↥(torusImage E (cNormalizer c)) := by
  rcases ctx.twelve with h | ⟨-, h⟩
  · exact h
  · exact absurd h hn12

theorem c_mem_E (ctx : Fus12Ctx G p A c L E) : c ∈ E := ctx.hyp.A_le_E ctx.hyp.c_mem

theorem c_not_mem_B (ctx : Fus12Ctx G p A c L E) :
    (⟨c, c_mem_E ctx⟩ : ↥E) ∉ (E ⊓ L).subgroupOf E := fun hmem =>
  ctx.c_not_mem (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hmem)).2

end Data

section Frame2

variable [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {b : G}
  {I X P Q : Subgroup G}

theorem exists_conjAut_mem_pCore (ctx : Fus12Ctx G p A c L E)
    (hnH : ¬ p ∣ Nat.card ↥(torusImage E (cNormalizer c)))
    {y : G} (hy : y ∈ Subgroup.normalizer (E : Set G)) (hyp : ∃ m : ℕ, y ^ (p ^ m) = 1) :
    ∃ w ∈ CFSG.pCore p ↥(torusWeyl E), ((w : ↥(torusWeyl E)) : MulAut E) = conjAut E y hy := by
  have hp : p.Prime := ctx.hyp.prime
  have hD := data_of_ctx ctx
  have hcE := c_mem_E ctx
  have hcB := c_not_mem_B ctx
  obtain ⟨m, hm⟩ := hyp
  have hφmem : conjAut E y hy ∈ torusWeyl E := ⟨⟨y, hy⟩, rfl⟩
  set φ : ↥(torusWeyl E) := ⟨conjAut E y hy, hφmem⟩ with hφ
  obtain ⟨x, hx, k, hk⟩ := hD.exists_mul_stabilizes hcB φ
  have hψ : ((x * φ : ↥(torusWeyl E)) : MulAut E) ∈ torusImage E (cNormalizer c) :=
    mem_torusImage_of_zpow hcE (x * φ).2 k hk
  have hφpow : φ ^ (p ^ m) = 1 := by
    have h1 : (⟨y, hy⟩ : ↥(Subgroup.normalizer (E : Set G))) ^ (p ^ m) = 1 :=
      Subtype.ext (by simpa using hm)
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    show conjAut E y hy ^ (p ^ m) = 1
    unfold conjAut
    rw [← map_pow, h1, map_one]
  have hXn : (CFSG.pCore p ↥(torusWeyl E)).Normal := CFSG.pCore_normal
  have hψX : (x * φ) ^ (p ^ m) ∈ CFSG.pCore p ↥(torusWeyl E) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff x).2 hx, one_mul, ← QuotientGroup.mk_pow, hφpow]
    rfl
  have hψpowH : (((x * φ) ^ (p ^ m) : ↥(torusWeyl E)) : MulAut E) ∈
      torusImage E (cNormalizer c) := by
    rw [Subgroup.coe_pow]
    exact pow_mem hψ _
  have hψpowX : (((x * φ) ^ (p ^ m) : ↥(torusWeyl E)) : MulAut E) ∈
      (CFSG.pCore p ↥(torusWeyl E)).map (torusWeyl E).subtype :=
    Subgroup.mem_map_of_mem _ hψX
  have h1 : (((x * φ) ^ (p ^ m) : ↥(torusWeyl E)) : MulAut E) = 1 := by
    have hmem : (((x * φ) ^ (p ^ m) : ↥(torusWeyl E)) : MulAut E) ∈
        (CFSG.pCore p ↥(torusWeyl E)).map (torusWeyl E).subtype ⊓ torusImage E (cNormalizer c) :=
      ⟨hψpowX, hψpowH⟩
    rw [ctx.eleven.2.2.2, Subgroup.mem_bot] at hmem
    exact hmem
  set γ : ↥(torusImage E (cNormalizer c)) := ⟨((x * φ : ↥(torusWeyl E)) : MulAut E), hψ⟩ with hγdef
  have hγ : γ ^ (p ^ m) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    have := h1
    rw [Subgroup.coe_pow] at this
    exact this
  have hγ1 : γ = 1 := Sec12Fus.eq_one_of_pow_eq_one_of_not_dvd hp hnH hγ
  have hψ1 : ((x * φ : ↥(torusWeyl E)) : MulAut E) = 1 := congrArg Subtype.val hγ1
  have hxφ : x * φ = 1 := Subtype.ext hψ1
  have hφx : φ = x⁻¹ := eq_inv_of_mul_eq_one_right hxφ
  refine ⟨x⁻¹, inv_mem hx, ?_⟩
  rw [← hφx]

theorem exists_mem_X_conjAut (hp : p.Prime) (hC : Choice1212 p E b I X P Q)
    {w : ↥(torusWeyl E)} (hw : w ∈ CFSG.pCore p ↥(torusWeyl E)) :
    ∃ x ∈ X, ∃ hx : x ∈ Subgroup.normalizer (E : Set G),
      conjAut E x hx = ((w : ↥(torusWeyl E)) : MulAut E) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set N := Subgroup.normalizer (E : Set G) with hN
  set ρ : ↥N →* MulAut E := E.normalizerMonoidHom with hρ
  set Xs := CFSG.pCore p ↥(torusWeyl E) with hXs
  set Xst : Subgroup (MulAut E) := Xs.map (torusWeyl E).subtype with hXst
  set N1 : Subgroup ↥N := Xst.comap ρ with hN1
  have hxP : xPreimage p E = N1.map N.subtype := rfl
  have hXx : X ≤ N1.map N.subtype := hC.X_sylow.1.1
  have hXN : X ≤ N := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hXx hx
    exact y.2
  let ρ1 : ↥N1 →* ↥Xst := (ρ.comp N1.subtype).codRestrict Xst (fun y => y.2)
  have hρ1 : Function.Surjective ρ1 := by
    rintro ⟨ξ, hξ⟩
    have hξW : ξ ∈ torusWeyl E := (Subgroup.map_subtype_le Xs) hξ
    obtain ⟨n, hn⟩ := hξW
    refine ⟨⟨n, ?_⟩, Subtype.ext hn⟩
    show ρ n ∈ Xst
    rw [hn]
    exact hξ
  set XN1 : Subgroup ↥N1 := (X.subgroupOf N).subgroupOf N1 with hXN1
  have hidx : ¬ p ∣ XN1.index := by
    have h1 := hC.X_sylow.1.2.2
    have h2 := Subgroup.relIndex_map_map_of_injective (X.subgroupOf N) N1 N.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hXN] at h2
    intro hdvd
    apply h1
    rw [hxP, h2]
    exact hdvd
  have hidx' : ¬ p ∣ (XN1.map ρ1).index := fun hd =>
    hidx (hd.trans (Subgroup.index_map_dvd XN1 hρ1))
  have hpg : IsPGroup p ↥Xst :=
    (CFSG.pCore_isPGroup (p := p) (G := ↥(torusWeyl E))).of_equiv
      (Subgroup.equivMapOfInjective Xs (torusWeyl E).subtype (torusWeyl E).subtype_injective)
  obtain ⟨n, hn⟩ := hpg.index (XN1.map ρ1)
  have hn0 : n = 0 := by
    by_contra hne
    exact hidx' (hn ▸ dvd_pow_self p hne)
  have htop : XN1.map ρ1 = ⊤ := by
    rw [← Subgroup.index_eq_one, hn, hn0, pow_zero]
  have hwst : (w : MulAut E) ∈ Xst := Subgroup.mem_map_of_mem _ hw
  have hmem : (⟨(w : MulAut E), hwst⟩ : ↥Xst) ∈ XN1.map ρ1 := by
    rw [htop]
    trivial
  obtain ⟨z, hzX, hz⟩ := Subgroup.mem_map.1 hmem
  have hzx : ((z : ↥N) : G) ∈ X := hzX
  refine ⟨(z : G), hzx, (z : ↥N).2, ?_⟩
  exact congrArg Subtype.val hz

theorem exists_regular (ctx : Fus12Ctx G p A c L E) (hC : Choice1212 p E b I X P Q)
    {e e' : G} (he : e ∈ E) (he' : e' ∈ E) (heL : e ∉ L) (he'L : e' ∉ L) :
    ∃ x ∈ X, ∃ k : ℤ, x * e * x⁻¹ = e' ^ k := by
  have hp : p.Prime := ctx.hyp.prime
  obtain ⟨φ, ⟨k, hk⟩, -⟩ := ctx.eleven.2.1 ⟨e, he⟩ ⟨e', he'⟩ heL he'L
  obtain ⟨x, hxX, hx, hxφ⟩ := exists_mem_X_conjAut hp hC φ.2
  refine ⟨x, hxX, k, ?_⟩
  have h1 := Equivariance.coe_conjAut hx ⟨e, he⟩
  rw [hxφ, hk] at h1
  rw [← h1]
  rfl

theorem fix_B (ctx : Fus12Ctx G p A c L E)
    (hnH : ¬ p ∣ Nat.card ↥(torusImage E (cNormalizer c))) (hC : Choice1212 p E b I X P Q)
    (hPE : P ≤ Subgroup.normalizer (E : Set G)) {x : G} (hx : x ∈ P) {z : G} (hz : z ∈ E ⊓ L) :
    x * z * x⁻¹ = z := by
  obtain ⟨m, hm⟩ := hC.P_sylow.1.2.1 ⟨x, hx⟩
  obtain ⟨w, hw, hwx⟩ := exists_conjAut_mem_pCore ctx hnH (hPE hx)
    ⟨m, congrArg Subtype.val hm⟩
  have hz' : z ∈ pCoreFixed p E := ctx.ten.1.ge hz
  obtain ⟨hzE, hfix⟩ := mem_pCoreFixed.1 hz'
  have h1 := hfix w hw
  rw [hwx] at h1
  have h2 := Equivariance.coe_conjAut (hPE hx) ⟨z, hzE⟩
  rw [h1] at h2
  exact h2.symm

theorem mod_B (ctx : Fus12Ctx G p A c L E)
    (hnH : ¬ p ∣ Nat.card ↥(torusImage E (cNormalizer c))) (hC : Choice1212 p E b I X P Q)
    (hPE : P ≤ Subgroup.normalizer (E : Set G)) {x : G} (hx : x ∈ P) {e : G} (he : e ∈ E) :
    x * e * x⁻¹ * e⁻¹ ∈ E ⊓ L := by
  obtain ⟨m, hm⟩ := hC.P_sylow.1.2.1 ⟨x, hx⟩
  obtain ⟨w, hw, hwx⟩ := exists_conjAut_mem_pCore ctx hnH (hPE hx)
    ⟨m, congrArg Subtype.val hm⟩
  have hD := data_of_ctx ctx
  have h1 := hD.mul_inv_mem hw ⟨e, he⟩
  have h2 := Subgroup.mem_subgroupOf.1 h1
  have h3 := Equivariance.coe_conjAut (hPE hx) ⟨e, he⟩
  have h4 : (((w : ↥(torusWeyl E)) : MulAut E) ⟨e, he⟩ : E) = ((conjAut E x (hPE hx) ⟨e, he⟩ : E)) := by
    rw [hwx]
  have h5 : ((((w : ↥(torusWeyl E)) : MulAut E) ⟨e, he⟩ * (⟨e, he⟩ : ↥E)⁻¹ : ↥E) : G) =
      x * e * x⁻¹ * e⁻¹ := by
    rw [Subgroup.coe_mul, h4, h3, Subgroup.coe_inv]
  rw [← h5]
  exact h2

end Frame2

end CFSG.RankThree.PartOne.K1214
