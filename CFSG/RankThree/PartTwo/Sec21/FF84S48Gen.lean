module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4BIso
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G]

theorem op2_le (H : Subgroup G) : Op 2 H ≤ H := by
  intro x hx
  have hx' : x ∈ (pCore 2 H).map H.subtype := hx
  obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hx'
  exact y.2

theorem op2_isPGroup (H : Subgroup G) : IsPGroup 2 (Op 2 H) := by
  intro g
  have hg2 : (g : G) ∈ (pCore 2 H).map H.subtype := g.2
  obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.1 hg2
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := H)) ⟨y, hy⟩
  have h2 : (y : G) ^ 2 ^ k = 1 := by
    have h1 := congrArg (fun z : ↥(pCore 2 H) => ((z : H) : G)) hk
    simpa using h1
  refine ⟨k, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [show (g : G) = (y : G) from hyg.symm]
  exact h2

theorem op2_of_normal {H N : Subgroup G} (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal)
    (hp : IsPGroup 2 N) : N ≤ Op 2 H := by
  have hp' : IsPGroup 2 (N.subgroupOf H) := by
    intro g
    obtain ⟨k, hk⟩ := hp ⟨(g : G), Subgroup.mem_subgroupOf.1 g.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have h1 := congrArg Subtype.val hk
    simpa using h1
  have hle : N.subgroupOf H ≤ pCore 2 H := le_sSup ⟨hN, hp'⟩
  intro x hx
  show x ∈ (pCore 2 H).map H.subtype
  exact Subgroup.mem_map.2 ⟨⟨x, hNH hx⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩

theorem op2_conj {H : Subgroup G} {g x : G} (hg : g ∈ H) (hx : x ∈ Op 2 H) :
    g * x * g⁻¹ ∈ Op 2 H := by
  have hx' : x ∈ (pCore 2 H).map H.subtype := hx
  show g * x * g⁻¹ ∈ (pCore 2 H).map H.subtype
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx'
  refine Subgroup.mem_map.2 ⟨(⟨g, hg⟩ : H) * y * (⟨g, hg⟩ : H)⁻¹, ?_, ?_⟩
  · exact (pCore_normal (p := 2) (G := H)).conj_mem y hy _
  · simp

theorem le_nor_op2 (H : Subgroup G) : H ≤ Nor (Op 2 H) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => op2_conj hg hx, fun hx => ?_⟩
  have := op2_conj (inv_mem hg) hx
  simpa [mul_assoc] using this

theorem normal_subgroupOf_of {H N : Subgroup G} (hH : H ≤ Nor N) (hNH : N ≤ H) :
    (N.subgroupOf H).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).2 hH

theorem mem_conjBy_iff {g x : G} {H : Subgroup G} : x ∈ conjBy g H ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem mem_conjBy_iff' {g x : G} {H : Subgroup G} : x ∈ conjBy g⁻¹ H ↔ g * x * g⁻¹ ∈ H := by
  rw [mem_conjBy_iff]; simp

theorem conjBy_conjBy_inv (g : G) (H : Subgroup G) : conjBy g (conjBy g⁻¹ H) = H := by
  ext x
  rw [mem_conjBy_iff, mem_conjBy_iff']
  simp [mul_assoc]

theorem conjBy_inv_conjBy (g : G) (H : Subgroup G) : conjBy g⁻¹ (conjBy g H) = H := by
  have := conjBy_conjBy_inv g⁻¹ H
  simpa using this

theorem conjBy_le_iff {g : G} {H K : Subgroup G} : conjBy g H ≤ conjBy g K ↔ H ≤ K := by
  constructor
  · intro h x hx
    have := h (mem_conjBy_iff.2 (by simpa [mul_assoc] using hx) : g * x * g⁻¹ ∈ conjBy g H)
    simpa [mem_conjBy_iff, mul_assoc] using this
  · intro h x hx
    rw [mem_conjBy_iff] at hx ⊢
    exact h hx

theorem card_conjBy (g : G) (H : Subgroup G) : Nat.card ↥(conjBy g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem mem_nor_conjBy {m g : G} {K : Subgroup G} : g ∈ Nor (conjBy m K) ↔ m⁻¹ * g * m ∈ Nor K := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h k
    have := h (m * k * m⁻¹)
    rw [mem_conjBy_iff, mem_conjBy_iff] at this
    simpa [mul_assoc] using this
  · intro h x
    rw [mem_conjBy_iff, mem_conjBy_iff]
    have := h (m⁻¹ * x * m)
    simpa [mul_assoc] using this

theorem conjBy_inf (g : G) (H K : Subgroup G) : conjBy g (H ⊓ K) = conjBy g H ⊓ conjBy g K := by
  ext x
  rw [Subgroup.mem_inf, mem_conjBy_iff, mem_conjBy_iff, mem_conjBy_iff, Subgroup.mem_inf]

theorem conjBy_cen {g x : G} : conjBy g (Cen x) = Cen (g * x * g⁻¹) := by
  ext y
  rw [mem_conjBy_iff, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : (g⁻¹ * y * g) * x = x * (g⁻¹ * y * g) := h
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h']
      _ = g * x * g⁻¹ * y := by group
  · intro h
    have h' : y * (g * x * g⁻¹) = g * x * g⁻¹ * y := h
    calc (g⁻¹ * y * g) * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * y) * g := by rw [h']
      _ = x * (g⁻¹ * y * g) := by group

theorem conjBy_closure_pair (g x y : G) :
    conjBy g (Subgroup.closure ({x, y} : Set G)) = Subgroup.closure ({g * x * g⁻¹, g * y * g⁻¹} : Set G) := by
  unfold conjBy
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  simp [MulAut.conj_apply]

theorem conjBy_zpowers (g x : G) : conjBy g (Subgroup.zpowers x) = Subgroup.zpowers (g * x * g⁻¹) := by
  unfold conjBy
  rw [MonoidHom.map_zpowers]
  simp [MulAut.conj_apply]

abbrev EA2 (H : Subgroup G) : Prop :=
  (∀ x ∈ H, ∀ y ∈ H, x * y = y * x) ∧ ∀ x ∈ H, x * x = 1

theorem EA2.mono {H K : Subgroup G} (h : EA2 K) (hHK : H ≤ K) : EA2 H :=
  ⟨fun x hx y hy => h.1 x (hHK hx) y (hHK hy), fun x hx => h.2 x (hHK hx)⟩

theorem EA2.of_isElemAb {H : Subgroup G} {k : ℕ} (h : IsElemAb 2 k H) : EA2 H := by
  obtain ⟨hEA, -⟩ := h
  haveI := hEA
  refine ⟨fun x hx y hy => congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : H) ⟨y, hy⟩),
    fun x hx => ?_⟩
  have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := H) x hx
  rwa [pow_two] at h

theorem EA2.isElemAb {H : Subgroup G} {k : ℕ} (h : EA2 H) (hc : Nat.card H = 2 ^ k) :
    IsElemAb 2 k H := by
  refine ⟨?_, hc⟩
  have hH : ∀ a : H, a ^ 2 = 1 := fun a => Subtype.ext (by simpa [pow_two] using h.2 a a.2)
  have hc : IsMulCommutative H := ⟨⟨fun a b => Subtype.ext (h.1 a a.2 b b.2)⟩⟩
  exact
    { toIsMulCommutative := hc
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hH }

theorem EA2.isPGroup {H : Subgroup G} (h : EA2 H) : IsPGroup 2 H := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  simpa [pow_two] using h.2 x x.2

theorem EA2.conj {H : Subgroup G} (h : EA2 H) (g : G) : EA2 (conjBy g H) := by
  constructor
  · intro x hx y hy
    rw [mem_conjBy_iff] at hx hy
    have := h.1 _ hx _ hy
    have e : g * (g⁻¹ * x * g * (g⁻¹ * y * g)) * g⁻¹ = x * y := by group
    have e' : g * (g⁻¹ * y * g * (g⁻¹ * x * g)) * g⁻¹ = y * x := by group
    rw [← e, ← e', this]
  · intro x hx
    rw [mem_conjBy_iff] at hx
    have := h.2 _ hx
    have e : g * (g⁻¹ * x * g * (g⁻¹ * x * g)) * g⁻¹ = x * x := by group
    rw [← e, this]; group

theorem exists_piStar_ge {X A V : Subgroup G} {q : ℕ} (hVX : V ≤ X) (hV : IsPGroup q V)
    (hA : A ≤ Nor V) : ∃ W ∈ PiStar X A q, V ≤ W := by
  obtain ⟨W, hVW, hW⟩ := Finite.exists_le_maximal
    (p := fun W : Subgroup G => W ≤ X ∧ IsPGroup q W ∧ A ≤ Nor W) (a := V) ⟨hVX, hV, hA⟩
  refine ⟨W, ⟨hW.1.1, hW.1.2.1, hW.1.2.2, fun V' hWV' hV'X hV'q hAV' => ?_⟩, hVW⟩
  exact (hW.eq_of_le ⟨hV'X, hV'q, hAV'⟩ hWV').symm

theorem piStar_conj {X A U : Subgroup G} {q : ℕ} {g : G} (hgX : g ∈ Nor X) (hgA : g ∈ Nor A)
    (hU : U ∈ PiStar X A q) : conjBy g U ∈ PiStar X A q := by
  obtain ⟨hUX, hUq, hAU, hmax⟩ := hU
  have hconjX : ∀ x ∈ X, g * x * g⁻¹ ∈ X := fun x hx => (Subgroup.mem_normalizer_iff.1 hgX x).1 hx
  have hconjX' : ∀ x ∈ X, g⁻¹ * x * g ∈ X := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hgX) x).1 hx
    simpa using this
  have hconjA : ∀ x ∈ A, g * x * g⁻¹ ∈ A := fun x hx => (Subgroup.mem_normalizer_iff.1 hgA x).1 hx
  have hconjA' : ∀ x ∈ A, g⁻¹ * x * g ∈ A := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hgA) x).1 hx
    simpa using this
  refine ⟨?_, hUq.map (MulAut.conj g).toMonoidHom, ?_, ?_⟩
  · intro x hx
    rw [mem_conjBy_iff] at hx
    have := hconjX _ (hUX hx)
    simpa [mul_assoc] using this
  · intro a ha
    rw [mem_nor_conjBy]
    exact hAU (hconjA' a ha)
  · intro V hUV hVX hVq hAV
    have h1 : U ≤ conjBy g⁻¹ V := by
      intro x hx
      rw [mem_conjBy_iff']
      apply hUV
      rw [mem_conjBy_iff]; simpa [mul_assoc] using hx
    have h2 : conjBy g⁻¹ V ≤ X := by
      intro x hx
      rw [mem_conjBy_iff'] at hx
      have := hconjX' _ (hVX hx)
      simpa [mul_assoc] using this
    have h3 : IsPGroup q (conjBy g⁻¹ V) := hVq.map (MulAut.conj g⁻¹).toMonoidHom
    have h4 : A ≤ Nor (conjBy g⁻¹ V) := by
      intro a ha
      rw [mem_nor_conjBy]
      apply hAV
      simpa using hconjA a ha
    have h5 := hmax _ h1 h2 h3 h4
    rw [← conjBy_conjBy_inv g V, h5]

open IsoAux

theorem decomp {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hsq : ∀ x ∈ S, x * x = 1) {c : G} (hc : c ∈ Nor S) (hc3 : c ^ 3 = 1) {x : G} (hx : x ∈ S) :
    ∃ f ∈ S ⊓ Cen c, ∃ d ∈ ⁅S, Subgroup.zpowers c⁆, x = f * d := by
  have hy : pim c x ∈ S := pim_mem hc hx
  have hfy : sg c (pim c x) = pim c x := pim_fix hcm hc hc3 hx
  have hcan : pim c (x * (pim c x)⁻¹) = 1 :=
    pim_cancel hcm hc hx hy (pim_of_fix hsq hy hfy) rfl
  have hwS : x * (pim c x)⁻¹ ∈ S := mul_mem hx (inv_mem hy)
  have hw : x * (pim c x)⁻¹ ∈ ⁅S, Subgroup.zpowers c⁆ := pim_ker hcm hsq hc hwS hcan
  refine ⟨pim c x, ⟨hy, ?_⟩, x * (pim c x)⁻¹, hw, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.2 (commute_of_sg hfy).eq.symm
  · have hcomm : x * (pim c x)⁻¹ * pim c x = pim c x * (x * (pim c x)⁻¹) := hcm _ hwS _ hy
    rw [← hcomm]; group

theorem comm_comm {S : Subgroup G} (hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hsq : ∀ x ∈ S, x * x = 1) {c : G} (hc : c ∈ Nor S) (hc3 : c ^ 3 = 1) :
    ⁅⁅S, Subgroup.zpowers c⁆, Subgroup.zpowers c⁆ = ⁅S, Subgroup.zpowers c⁆ := by
  set T := ⁅S, Subgroup.zpowers c⁆ with hT
  have hTS : T ≤ S := W_le_S hcm hsq hc hc3
  have hcmT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy => hcm x (hTS hx) y (hTS hy)
  have hsqT : ∀ x ∈ T, x * x = 1 := fun x hx => hsq x (hTS hx)
  have hrange := commutator_zpowers_eq_range hcm hsq hc hc3
  have hcT : c ∈ Nor T := by
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ x ∈ T, c * x * c⁻¹ ∈ T := by
      intro x hx
      rw [hT, hrange] at hx
      obtain ⟨y, rfl⟩ := hx
      rw [hT, hrange]
      refine ⟨⟨sg c y, sg_mem hc y.2⟩, ?_⟩
      rw [phiHom_apply, phiHom_apply]
      show (sg c y)⁻¹ * sg c (sg c y) = sg c ((y : G)⁻¹ * sg c y)
      simp only [sg]; group
    intro x
    refine ⟨key x, fun hx => ?_⟩
    have h2 := key _ (key _ hx)
    have hc3' : c * c * c = 1 := by simpa [pow_succ] using hc3
    have e : c * (c * (c * x * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * x * (c * c * c)⁻¹ := by group
    rw [e, hc3'] at h2
    simpa using h2
  have hpim : ∀ x ∈ T, pim c x = 1 := by
    intro x hx
    rw [hT, hrange] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [phiHom_apply]
    have hc3' : c * c * c = 1 := by simpa [pow_succ] using hc3
    have e : pim c ((y : G)⁻¹ * sg c y) =
        (y : G)⁻¹ * ((c * c * c) * (y : G) * (c * c * c)⁻¹) := by
      simp only [pim, sg]; group
    rw [e, hc3']; group
  refine le_antisymm (W_le_S hcmT hsqT hcT hc3) fun x hx => ?_
  exact pim_ker hcmT hsqT hcT hx (hpim x hx)

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
