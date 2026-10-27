module

public import CFSG.Walter.W67.Section8.CentralLift
public import CFSG.Walter.W67.Section8.Lemma81
public import CFSG.Walter.W67.W2Basic

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups

namespace Lemma82

variable {G : Type} [Group G] {L : Type} [Group L]

@[expose] noncomputable def proj (Z : Subgroup G) [Z.Normal] (e : (G ⧸ Z) ≃* L) : G →* L :=
  e.toMonoidHom.comp (QuotientGroup.mk' Z)

theorem proj_surjective (Z : Subgroup G) [Z.Normal] (e : (G ⧸ Z) ≃* L) :
    Function.Surjective (proj Z e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective Z)

theorem ker_proj (Z : Subgroup G) [Z.Normal] (e : (G ⧸ Z) ≃* L) : (proj Z e).ker = Z := by
  ext x
  simp only [proj, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    QuotientGroup.mk'_apply]
  rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]

theorem exists_eq_zpowers {X : Type*} [Group X] (H : Subgroup X) [IsCyclic H] :
    ∃ g : X, H = Subgroup.zpowers g := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  refine ⟨g, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := hg ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · rintro ⟨k, rfl⟩
    exact H.zpow_mem g.2 k

theorem map_conj_eq_of_mem_normalizer {X : Type*} [Group X] {H : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (H : Set X)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
    simpa [mul_assoc] using this

theorem oddMultiplier_of_eq {p : ℕ} [Fact p.Prime] (hp : p = 3) {n : ℕ} (hn : Odd n)
    (h : S_psl2_three_oddMultiplier) : OddMultiplierTrivial (PSL(2, GaloisField p n)) := by
  subst hp
  exact h n hn

theorem p_eq_three_and_odd_f [Finite L] (hL : JRGroup L) (hR1 : hL.R1) :
    hL.p = 3 ∧ Odd hL.f := by
  obtain ⟨⟨n, hn, hqn⟩, -⟩ := hR1
  have hq : hL.p ^ hL.f = 3 ^ n := hqn
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by decide)
  have h3 : 3 ∣ hL.p := by
    have : 3 ∣ hL.p ^ hL.f := by rw [hq]; exact dvd_pow_self 3 hn0
    exact Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
  have hp : hL.p = 3 :=
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : hL.p.Prime)).mp h3).symm
  refine ⟨hp, ?_⟩
  rw [hp] at hq
  have hfn : hL.f = n := Nat.pow_right_injective (by norm_num : 2 ≤ 3) hq
  rw [hfn]
  exact hn

section Construction

variable [Finite L] (hL : JRGroup L) (Z : Subgroup G) [Z.Normal] (e : (G ⧸ Z) ≃* L)

@[expose] noncomputable def Ktil : Subgroup G := hL.K.comap (proj Z e)

@[expose] noncomputable def K₀ : Subgroup G := ⁅Ktil hL Z e, Ktil hL Z e⁆

theorem map_Ktil : (Ktil hL Z e).map (proj Z e) = hL.K :=
  Subgroup.map_comap_eq_self_of_surjective (proj_surjective Z e) _

theorem map_K₀ (hq : 3 < hL.q) : (K₀ hL Z e).map (proj Z e) = hL.K := by
  rw [K₀, Subgroup.map_commutator, map_Ktil]
  exact PSL2Sub.commutator_eq hL.iso hL.f_pos hq

theorem K₀_le_Ktil : K₀ hL Z e ≤ Ktil hL Z e := Subgroup.commutator_le_self _

theorem Ktil_eq (hq : 3 < hL.q) : Ktil hL Z e = K₀ hL Z e ⊔ Z := by
  have h := Subgroup.comap_map_eq (proj Z e) (K₀ hL Z e)
  rw [map_K₀ hL Z e hq, ker_proj] at h
  exact h

theorem commutator_K₀ (hq : 3 < hL.q) (hZc : Z ≤ Subgroup.center G) :
    ⁅K₀ hL Z e, K₀ hL Z e⁆ = K₀ hL Z e := by
  rw [← CentralLift.commutator_sup_eq hZc, ← Ktil_eq hL Z e hq]
  rfl

@[expose] noncomputable def psi : K₀ hL Z e →* hL.K :=
  ((proj Z e).comp (K₀ hL Z e).subtype).codRestrict hL.K
    (fun x => K₀_le_Ktil hL Z e x.2)

theorem psi_apply (x : K₀ hL Z e) : (psi hL Z e x : L) = proj Z e x := rfl

theorem psi_surjective (hq : 3 < hL.q) : Function.Surjective (psi hL Z e) := by
  intro y
  have hy : (y : L) ∈ (K₀ hL Z e).map (proj Z e) := by rw [map_K₀ hL Z e hq]; exact y.2
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

theorem ker_psi : (psi hL Z e).ker = Z.subgroupOf (K₀ hL Z e) := by
  ext x
  have hk : proj Z e x = 1 ↔ (x : G) ∈ Z := by rw [← MonoidHom.mem_ker, ker_proj]
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hk]
  constructor
  · intro h
    have := congrArg Subtype.val h
    rwa [psi_apply] at this
  · intro h
    exact Subtype.ext (by rw [psi_apply]; exact h)

theorem K₀_inf_eq_bot [Finite G] (hq : 3 < hL.q) (hR1 : hL.R1)
    (hZc : Z ≤ Subgroup.center G) (hZo : Odd (Nat.card Z)) (hM : S_psl2_three_oddMultiplier) :
    K₀ hL Z e ⊓ Z = ⊥ := by
  obtain ⟨hp3, hfodd⟩ := p_eq_three_and_odd_f hL hR1
  have hmult := oddMultiplier_of_eq hp3 hfodd hM
  set Z' : Subgroup (K₀ hL Z e) := Z.subgroupOf (K₀ hL Z e) with hZ'
  have : Z'.Normal := Subgroup.Normal.subgroupOf ‹_› _
  have hZ'c : Z' ≤ Subgroup.center (K₀ hL Z e) := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hZc (Subgroup.mem_subgroupOf.mp hz))) k)
  have hZ'o : Odd (Nat.card Z') := by
    have h1 : Nat.card Z' = Nat.card (Z'.map (K₀ hL Z e).subtype) :=
      (Subgroup.card_map_of_injective (K₀ hL Z e).subtype_injective).symm
    have h2 : Z'.map (K₀ hL Z e).subtype ≤ Z := by
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hx
    rw [h1]
    exact Odd.of_dvd_nat hZo (Subgroup.card_dvd_of_le h2)
  have hperf : commutator (K₀ hL Z e) = ⊤ := by
    apply Subgroup.map_injective (K₀ hL Z e).subtype_injective
    rw [Subgroup.map_subtype_commutator, commutator_K₀ hL Z e hq hZc, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hiso : Nonempty ((K₀ hL Z e ⧸ Z') ≃* PSL(2, GaloisField hL.p hL.f)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq (ker_psi hL Z e).symm).trans
      ((QuotientGroup.quotientKerEquivOfSurjective _ (psi_surjective hL Z e hq)).trans hL.iso)⟩
  have hbot := hmult (K₀ hL Z e) Z' hZ'c hZ'o hperf hiso
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx.1⟩ : K₀ hL Z e) ∈ Z' := Subgroup.mem_subgroupOf.mpr hx.2
  rw [hbot, Subgroup.mem_bot] at this
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)

@[expose] noncomputable def isoK₀ [Finite G] (hq : 3 < hL.q) (hR1 : hL.R1)
    (hZc : Z ≤ Subgroup.center G) (hZo : Odd (Nat.card Z)) (hM : S_psl2_three_oddMultiplier) :
    K₀ hL Z e ≃* hL.K :=
  MulEquiv.ofBijective (psi hL Z e) ⟨by
    rw [← MonoidHom.ker_eq_bot_iff, ker_psi, eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ K₀ hL Z e ⊓ Z := ⟨x.2, Subgroup.mem_subgroupOf.mp hx⟩
    rw [K₀_inf_eq_bot hL Z e hq hR1 hZc hZo hM, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).mpr (Subtype.ext hx'), psi_surjective hL Z e hq⟩

theorem isoK₀_apply [Finite G] (hq : 3 < hL.q) (hR1 : hL.R1) (hZc : Z ≤ Subgroup.center G)
    (hZo : Odd (Nat.card Z)) (hM : S_psl2_three_oddMultiplier) (x : K₀ hL Z e) :
    (isoK₀ hL Z e hq hR1 hZc hZo hM x : L) = proj Z e x := rfl

theorem mem_normalizer_K₀ {g : G} (hg : proj Z e g ∈ Subgroup.normalizer (hL.K : Set L)) :
    g ∈ Subgroup.normalizer (K₀ hL Z e : Set G) := by
  have hgK : g ∈ Subgroup.normalizer (Ktil hL Z e : Set G) :=
    Subgroup.le_normalizer_comap (proj Z e) hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => conj_mem_commutator_of_mem_normalizer hgK hx
  · intro hx
    have h := conj_mem_commutator_of_mem_normalizer (Subgroup.inv_mem _ hgK) hx
    have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rw [h2] at h
    exact h

theorem centralizer_le_normalizer_K :
    Subgroup.centralizer ({hL.J} : Set L) ≤ Subgroup.normalizer (hL.K : Set L) := by
  rw [hL.centralizer_eq]
  refine sup_le ?_ (Subgroup.le_normalizer)
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  intro y
  have hc : ∀ k ∈ hL.K, hL.J * k * hL.J⁻¹ = k := by
    intro k hk
    have := Subgroup.mem_centralizer_singleton_iff.mp (hL.le_centralizer hk)
    rw [← this]
    group
  have hc' : ∀ k ∈ hL.K, hL.J⁻¹ * k * hL.J = k := by
    intro k hk
    calc hL.J⁻¹ * k * hL.J = hL.J⁻¹ * (hL.J * k * hL.J⁻¹) * hL.J := by rw [hc k hk]
      _ = k := by group
  constructor
  · intro hy
    rw [hc y hy]
    exact hy
  · intro hy
    have h2 : y = hL.J⁻¹ * (hL.J * y * hL.J⁻¹) * hL.J := by group
    rw [h2, hc' _ hy]
    exact hy

theorem K₀_le_centralizer [Finite G] (hq : 3 < hL.q) (hR1 : hL.R1)
    (hZc : Z ≤ Subgroup.center G) (hZo : Odd (Nat.card Z)) (hM : S_psl2_three_oddMultiplier)
    {J : G} (hJ : proj Z e J = hL.J) : K₀ hL Z e ≤ Subgroup.centralizer ({J} : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hJN : J ∈ Subgroup.normalizer (K₀ hL Z e : Set G) := by
    apply mem_normalizer_K₀
    rw [hJ]
    exact centralizer_le_normalizer_K hL (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have h1 : J * k * J⁻¹ * k⁻¹ ∈ K₀ hL Z e :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hJN k).mp hk) (Subgroup.inv_mem _ hk)
  have h2 : J * k * J⁻¹ * k⁻¹ ∈ Z := by
    rw [← ker_proj Z e, MonoidHom.mem_ker]
    have hkL : proj Z e k ∈ hL.K := K₀_le_Ktil hL Z e hk
    have := Subgroup.mem_centralizer_singleton_iff.mp (hL.le_centralizer hkL)
    simp only [map_mul, map_inv, hJ]
    rw [← this]
    group
  have h3 : J * k * J⁻¹ * k⁻¹ ∈ K₀ hL Z e ⊓ Z := ⟨h1, h2⟩
  rw [K₀_inf_eq_bot hL Z e hq hR1 hZc hZo hM, Subgroup.mem_bot] at h3
  calc k * J = (J * k * J⁻¹ * k⁻¹)⁻¹ * (J * k) := by group
    _ = J * k := by rw [h3, inv_one, one_mul]

theorem K₀_normal [Finite G] (hZc : Z ≤ Subgroup.center G) (hZo : Odd (Nat.card Z)) {J : G}
    (hJ : proj Z e J = hL.J) (hJ2 : orderOf J = 2) :
    ((K₀ hL Z e).subgroupOf (Subgroup.centralizer ({J} : Set G))).Normal := by
  constructor
  intro n hn c
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hc : proj Z e c ∈ Subgroup.centralizer ({hL.J} : Set L) := by
    have := (CentralLift.centralizer_eq_comap (proj Z e) (ker_proj Z e) hZc hZo hJ2).le c.2
    rwa [Subgroup.mem_comap, hJ] at this
  have hcN := mem_normalizer_K₀ hL Z e (centralizer_le_normalizer_K hL hc)
  exact (Subgroup.mem_normalizer_iff.mp hcN n).mp hn

include hL e in
theorem sylow_facts [Finite G] (hZo : Odd (Nat.card Z)) (P : Sylow 2 G) :
    IsMulCommutative (P : Subgroup G) ∧ Nat.card (P : Subgroup G) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2⟩ :=
    CentralLift.card_map_sylow (proj Z e) (proj_surjective Z e) (ker_proj Z e) hZo P
  let Q : Sylow 2 L := Sylow.ofCard _ h2
  have hQ : (Q : Subgroup L) = (P : Subgroup G).map (proj Z e) := Sylow.coe_ofCard _ _
  have hab : IsMulCommutative (Q : Subgroup L) := (hL.elementary_sylow Q).toIsMulCommutative
  have h8 : Nat.card (Q : Subgroup L) = 8 := hL.card_sylow Q
  have hPZ := CentralLift.inf_eq_bot_of_isPGroup hZo P.isPGroup'
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · apply Subtype.ext
    apply CentralLift.eq_of_inf_eq_bot (proj Z e) (ker_proj Z e) hPZ
      ((P : Subgroup G).mul_mem a.2 b.2) ((P : Subgroup G).mul_mem b.2 a.2)
    have ha : proj Z e a ∈ (Q : Subgroup L) := by rw [hQ]; exact ⟨a, a.2, rfl⟩
    have hb : proj Z e b ∈ (Q : Subgroup L) := by rw [hQ]; exact ⟨b, b.2, rfl⟩
    have := hab.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩
    simpa [map_mul] using congrArg Subtype.val this
  · rw [← h1, ← hQ, h8]

@[expose] noncomputable def hyp [Finite G] (hq : 3 < hL.q) (hR1 : hL.R1)
    (hZc : Z ≤ Subgroup.center G) (hZo : Odd (Nat.card Z)) (hM : S_psl2_three_oddMultiplier)
    (J : G) (hJ : proj Z e J = hL.J) (hJ2 : orderOf J = 2) : Hyp G where
  p := hL.p
  f := hL.f
  p_ne_two := hL.p_ne_two
  f_pos := hL.f_pos
  abelian_sylow P := (sylow_facts hL Z e hZo P).1
  card_sylow P := (sylow_facts hL Z e hZo P).2
  J := J
  orderOf_J := hJ2
  K := K₀ hL Z e
  le_centralizer := K₀_le_centralizer hL Z e hq hR1 hZc hZo hM hJ
  normal := K₀_normal hL Z e hZc hZo hJ hJ2
  iso := (isoK₀ hL Z e hq hR1 hZc hZo hM).trans hL.iso

omit [Finite L] in
theorem mem_normalizer_of_map [Finite G] (hZc : Z ≤ Subgroup.center G) (hZo : Odd (Nat.card Z))
    {W : Subgroup G} (hW : IsPGroup 2 W) {g : G}
    (hg : proj Z e g ∈ Subgroup.normalizer ((W.map (proj Z e) : Subgroup L) : Set L)) :
    g ∈ Subgroup.normalizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W' := W.map (MulAut.conj g).toMonoidHom with hW'
  have hW'2 : IsPGroup 2 W' := hW.map _
  have hle : W' ≤ (W.map (proj Z e)).comap (proj Z e) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_comap]
    have : proj Z e (MulAut.conj g w) = proj Z e g * proj Z e w * (proj Z e g)⁻¹ := by
      simp [MulAut.conj_apply]
    rw [MulEquiv.coe_toMonoidHom, this]
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp ⟨w, hw, rfl⟩
  have hcard : Nat.card W' = Nat.card W :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq := CentralLift.eq_of_isPGroup_le_comap (proj Z e) (ker_proj Z e) hZc hZo hW hW'2 hle
    hcard
  refine JT.mem_normalizer_of_conj_mem fun x hx => ?_
  have : g * x * g⁻¹ ∈ W' := ⟨x, hx, by simp [MulAut.conj_apply]⟩
  rwa [heq] at this

section Frame

variable [Finite G] (hq : 3 < hL.q) (hR1 : hL.R1) (hZc : Z ≤ Subgroup.center G)
  (hZo : Odd (Nat.card Z)) (hM : S_psl2_three_oddMultiplier) {J : G}
  (hJ : proj Z e J = hL.J) (hJ2 : orderOf J = 2)

theorem E_eq (hR2 : hL.R2) (fr : Frame (hyp hL Z e hq hR1 hZc hZo hM J hJ hJ2)) :
    fr.E = Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Subgroup G := (fr.S : Subgroup G) with hSdef
  obtain ⟨h1, h2⟩ :=
    CentralLift.card_map_sylow (proj Z e) (proj_surjective Z e) (ker_proj Z e) hZo fr.S
  let Q : Sylow 2 L := Sylow.ofCard _ h2
  have hQ : (Q : Subgroup L) = S.map (proj Z e) := Sylow.coe_ofCard _ _
  have hCQ := (hR2.1 Q).1
  have hZn : Z.Normal := ‹_›
  have hCS : fr.CS = S ⊔ Z := by
    apply le_antisymm
    · intro x hx
      have hxQ : proj Z e x ∈ Subgroup.centralizer ((Q : Subgroup L) : Set L) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [hQ] at hy
        obtain ⟨s, hs, rfl⟩ := hy
        rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hx) s hs]
      rw [hCQ, hQ] at hxQ
      have := Subgroup.mem_comap.mpr hxQ
      rwa [Subgroup.comap_map_eq, ker_proj] at this
    · refine sup_le ?_ ?_
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hab := (sylow_facts hL Z e hZo fr.S).1
        exact congrArg Subtype.val (hab.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
      · intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact Subgroup.mem_center_iff.mp (hZc hz) y
  change oddPart fr.CS = Z
  rw [hCS]
  apply le_antisymm
  · rintro x hx
    have hxo := odd_orderOf_of_mem_oddPart hx
    have hxY := oddPart_le _ hx
    obtain ⟨s, hs, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hxY
    have hcomm : Commute s z := Subgroup.mem_center_iff.mp (hZc hz) s
    have hzo : Odd (orderOf z) := by
      have hd : orderOf z ∣ Nat.card Z := by
        rw [← Subgroup.orderOf_mk z hz]
        exact orderOf_dvd_natCard _
      exact Odd.of_dvd_nat hZo hd
    have hso : Odd (orderOf s) := by
      have hcomm' : Commute (s * z) z⁻¹ := ((hcomm.mul_left (Commute.refl z))).inv_right
      have hdvd : orderOf ((s * z) * z⁻¹) ∣ orderOf (s * z) * orderOf z⁻¹ :=
        hcomm'.orderOf_mul_dvd_mul_orderOf
      rw [mul_inv_cancel_right, orderOf_inv] at hdvd
      exact Odd.of_dvd_nat (hxo.mul hzo) hdvd
    have hs1 : s = 1 := eq_one_of_odd_of_isPGroup fr.S.isPGroup' hs hso
    rw [hs1, one_mul]
    exact hz
  · intro z hz
    have hN : (Z.subgroupOf (S ⊔ Z)).Normal := hZn.subgroupOf _
    have hcop : Nat.Coprime 2 (Nat.card (Z.subgroupOf (S ⊔ Z))) := by
      have : Nat.card (Z.subgroupOf (S ⊔ Z)) = Nat.card Z :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
      rw [this]
      exact Nat.coprime_two_left.mpr hZo
    have hle := CFSG.le_pPrimeCore_of_normal_coprime hN hcop
    exact ⟨⟨z, (le_sup_right : Z ≤ S ⊔ Z) hz⟩, hle (Subgroup.mem_subgroupOf.mpr hz), rfl⟩

include hR1 in
theorem q_mod_eight_of_R1 : hL.p ^ hL.f % 8 = 3 := by
  obtain ⟨hp3, hfodd⟩ := p_eq_three_and_odd_f hL hR1
  rw [hp3]
  exact Lemma81.three_pow_mod_eight_of_odd hfodd

section A

variable (fr : Frame (hyp hL Z e hq hR1 hZc hZo hM J hJ hJ2)) {T₂ : G} (hT : T₂ ∈ fr.T)
  (hT2 : orderOf T₂ = 2)

include hT in
theorem T₂_mem_K₀ : T₂ ∈ K₀ hL Z e := fr.T_le_K hT

include hT in
theorem t_mem_K : proj Z e T₂ ∈ hL.K := K₀_le_Ktil hL Z e (T₂_mem_K₀ hL Z e hq hR1 hZc hZo hM hJ
  hJ2 fr hT)

include hT hT2 in
theorem orderOf_t : orderOf (proj Z e T₂) = 2 := by
  rw [CentralLift.orderOf_map_of_inf_eq_bot (proj Z e) (ker_proj Z e)
    (K₀_inf_eq_bot hL Z e hq hR1 hZc hZo hM) (T₂_mem_K₀ hL Z e hq hR1 hZc hZo hM hJ hJ2 fr hT),
    hT2]

include hT hT2 in
theorem mem_A_iff {y : G} :
    y ∈ fr.A T₂ ↔ y ∈ K₀ hL Z e ⊓ Subgroup.centralizer ({T₂} : Set G) ∧ Odd (orderOf y) := by
  constructor
  · intro hy
    exact ⟨oddPart_le _ hy, odd_orderOf_of_mem_oddPart hy⟩
  · rintro ⟨hy, hodd⟩
    exact Lemma81.mem_oddPart_inf_centralizer (hyp hL Z e hq hR1 hZc hZo hM J hJ hJ2).iso
      (hyp hL Z e hq hR1 hZc hZo hM J hJ hJ2).odd_p (hyp hL Z e hq hR1 hZc hZo hM J hJ hJ2).f_pos
      (q_mod_eight_of_R1 hL hR1) (T₂_mem_K₀ hL Z e hq hR1 hZc hZo hM hJ hJ2 fr hT) hT2 hy hodd

include hT hT2 in
theorem mem_AL_iff {a : L} :
    a ∈ oddPart (hL.K ⊓ Subgroup.centralizer ({proj Z e T₂} : Set L)) ↔
      a ∈ hL.K ⊓ Subgroup.centralizer ({proj Z e T₂} : Set L) ∧ Odd (orderOf a) := by
  constructor
  · intro ha
    exact ⟨oddPart_le _ ha, odd_orderOf_of_mem_oddPart ha⟩
  · rintro ⟨ha, hodd⟩
    exact Lemma81.mem_oddPart_inf_centralizer hL.iso
      ((Fact.out : hL.p.Prime).odd_of_ne_two hL.p_ne_two) hL.f_pos (q_mod_eight_of_R1 hL hR1)
      (t_mem_K hL Z e hq hR1 hZc hZo hM hJ hJ2 fr hT)
      (orderOf_t hL Z e hq hR1 hZc hZo hM hJ hJ2 fr hT hT2) ha hodd

theorem A_le_K₀ : fr.A T₂ ≤ K₀ hL Z e := fun _ hy => (oddPart_le _ hy).1

include hT hT2 in
theorem map_A :
    (fr.A T₂).map (proj Z e) = oddPart (hL.K ⊓ Subgroup.centralizer ({proj Z e T₂} : Set L)) := by
  have hKZ := K₀_inf_eq_bot hL Z e hq hR1 hZc hZo hM
  have hT₂K := T₂_mem_K₀ hL Z e hq hR1 hZc hZo hM hJ hJ2 fr hT
  ext a
  rw [mem_AL_iff hL Z e hq hR1 hZc hZo hM hJ hJ2 fr hT hT2]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyKC, hodd⟩ := (mem_A_iff hL Z e hq hR1 hZc hZo hM hJ hJ2 fr hT hT2).mp hy
    have hyK := (Subgroup.mem_inf.mp hyKC).1
    have hyT := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hyKC).2
    refine ⟨Subgroup.mem_inf.mpr ⟨K₀_le_Ktil hL Z e hyK, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hyT]
    · rwa [CentralLift.orderOf_map_of_inf_eq_bot (proj Z e) (ker_proj Z e) hKZ hyK]
  · rintro ⟨haKC, hodd⟩
    have haK := (Subgroup.mem_inf.mp haKC).1
    have haT := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp haKC).2
    have ha : a ∈ (K₀ hL Z e).map (proj Z e) := by rw [map_K₀ hL Z e hq]; exact haK
    obtain ⟨y, hyK, rfl⟩ := ha
    refine ⟨y, (mem_A_iff hL Z e hq hR1 hZc hZo hM hJ hJ2 fr hT hT2).mpr
      ⟨Subgroup.mem_inf.mpr ⟨hyK, ?_⟩, ?_⟩, rfl⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      apply CentralLift.eq_of_inf_eq_bot (proj Z e) (ker_proj Z e) hKZ
        ((K₀ hL Z e).mul_mem hyK hT₂K) ((K₀ hL Z e).mul_mem hT₂K hyK)
      rw [map_mul, map_mul]
      exact haT
    · rwa [CentralLift.orderOf_map_of_inf_eq_bot (proj Z e) (ker_proj Z e) hKZ hyK] at hodd

theorem A_inf_eq_bot : fr.A T₂ ⊓ Z = ⊥ :=
  le_bot_iff.mp ((inf_le_inf_right Z (A_le_K₀ hL Z e hq hR1 hZc hZo hM hJ hJ2 fr)).trans
    (K₀_inf_eq_bot hL Z e hq hR1 hZc hZo hM).le)

theorem card_map_A : Nat.card ((fr.A T₂).map (proj Z e)) = Nat.card (fr.A T₂) := by
  have hinj := CentralLift.injective_restrict (proj Z e) (ker_proj Z e)
    (A_inf_eq_bot hL Z e hq hR1 hZc hZo hM hJ hJ2 fr (T₂ := T₂))
  have := Subgroup.card_map_of_injective (K := ⊤) hinj
  rw [Subgroup.card_top] at this
  rw [← this, ← MonoidHom.range_eq_map, MonoidHom.range_comp, Subgroup.range_subtype]

theorem isCyclic_A (hc : IsCyclic ((fr.A T₂).map (proj Z e))) : IsCyclic (fr.A T₂) := by
  have hinj := CentralLift.injective_restrict (proj Z e) (ker_proj Z e)
    (A_inf_eq_bot hL Z e hq hR1 hZc hZo hM hJ hJ2 fr (T₂ := T₂))
  have hr : ((proj Z e).comp (fr.A T₂).subtype).range = (fr.A T₂).map (proj Z e) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e1 : fr.A T₂ ≃* ((proj Z e).comp (fr.A T₂).subtype).range := MonoidHom.ofInjective hinj
  have : IsCyclic ((proj Z e).comp (fr.A T₂).subtype).range := by
    rw [hr]; exact hc
  exact isCyclic_of_surjective _ e1.symm.surjective

end A

end Frame

end Construction

end Lemma82


open Lemma82 in
theorem lemma_8_2_of
    (hM : S_psl2_three_oddMultiplier) (h43ab : S_prop_4_3_ab) :
    S_lemma_8_2 := by
  intro G _ _ L _ _ hL hq ⟨hR1, hR2, hR4⟩ Z _ hZc hZo _ hperf e
  obtain ⟨J, hJ, hJ2⟩ := CentralLift.exists_involution (proj Z e) (proj_surjective Z e)
    (ker_proj Z e) hZo hL.orderOf_J
  obtain ⟨fr⟩ := Frame.nonempty G (hyp hL Z e hq hR1 hZc hZo hM J hJ hJ2)
  have hE : fr.E = Z := E_eq hL Z e hq hR1 hZc hZo hM hJ hJ2 hR2 fr
  have hidx := Lemma81.index_ne_two_of_perfect hperf
  obtain ⟨hp3, hfodd⟩ := p_eq_three_and_odd_f hL hR1
  have hf1 : 1 < hL.f := by
    have : 3 < 3 ^ hL.f := by
      have h3 : hL.q = 3 ^ hL.f := by
        change hL.p ^ hL.f = 3 ^ hL.f
        rw [hp3]
      rw [← h3]; exact hq
    by_contra h1
    interval_cases h : hL.f
    · norm_num at this
    · norm_num at this
  obtain ⟨T₂, hT, hT2⟩ := Lemma81.exists_involution_T fr
  obtain ⟨U, hU3, hNV, hUE, hUV, -, hCV, hT1A, -⟩ :=
    h43ab G (hyp hL Z e hq hR1 hZc hZo hM J hJ hJ2) fr hp3 hidx hT hT2
  have htK := t_mem_K hL Z e hq hR1 hZc hZo hM hJ hJ2 fr hT
  have ht2 := orderOf_t hL Z e hq hR1 hZc hZo hM hJ hJ2 fr hT hT2
  obtain ⟨hcyc, hcardA, -, SL, UL, -, -, -, hNVA, -, -, -, -, -, hCa⟩ :=
    hR4 hq (proj Z e T₂) htK ht2
  set AL := oddPart (hL.K ⊓ Subgroup.centralizer ({proj Z e T₂} : Set L)) with hAL
  set VL := Subgroup.closure ({hL.J, proj Z e T₂} : Set L) with hVL
  have hmapA := map_A hL Z e hq hR1 hZc hZo hM hJ hJ2 fr hT hT2
  have hmapV : (fr.V T₂).map (proj Z e) = VL := by
    change (Subgroup.closure {J, T₂}).map (proj Z e) = _
    rw [MonoidHom.map_closure, Set.image_pair, hJ]
  have hAcyc : IsCyclic (fr.A T₂) :=
    isCyclic_A hL Z e hq hR1 hZc hZo hM hJ hJ2 fr (by rw [hmapA]; exact hcyc)
  have hAinf := A_inf_eq_bot hL Z e hq hR1 hZc hZo hM hJ hJ2 fr (T₂ := T₂)
  have hVS : fr.V T₂ ≤ (fr.S : Subgroup G) := by
    change Subgroup.closure {J, T₂} ≤ _
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact fr.J_mem
    · exact fr.T_le_S hT
  have hV2 : IsPGroup 2 (fr.V T₂) := fr.S.isPGroup'.to_le hVS
  have hgen : ∀ Aα : Subgroup G, Aα ≤ fr.A T₂ → Aα ≠ ⊥ → ∃ a ∈ AL, a ≠ 1 ∧
      Aα.map (proj Z e) = Subgroup.zpowers a := by
    intro Aα hle hne
    have hle' : Aα.map (proj Z e) ≤ AL := by
      rw [hAL, ← hmapA]
      exact Subgroup.map_mono hle
    have : IsCyclic (Aα.map (proj Z e)) :=
      isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hle').surjective
    obtain ⟨a, ha⟩ := exists_eq_zpowers (Aα.map (proj Z e))
    refine ⟨a, hle' (ha ▸ Subgroup.mem_zpowers a), ?_, ha⟩
    rintro rfl
    apply hne
    rw [Subgroup.zpowers_one_eq_bot] at ha
    have hAαZ : Aα ⊓ Z = ⊥ := le_bot_iff.mp ((inf_le_inf_right Z hle).trans hAinf.le)
    rw [eq_bot_iff]
    intro x hx
    have : proj Z e x = 1 := by
      have : proj Z e x ∈ Aα.map (proj Z e) := ⟨x, hx, rfl⟩
      rwa [ha, Subgroup.mem_bot] at this
    have hxZ : x ∈ Aα ⊓ Z := ⟨hx, by rw [← ker_proj Z e]; exact this⟩
    rwa [hAαZ] at hxZ
  have hCVA : Subgroup.centralizer (fr.V T₂ : Set G) ≤ Subgroup.normalizer (fr.A T₂ : Set G) := by
    intro c hc
    have hJV : J ∈ fr.V T₂ := Subgroup.subset_closure (Set.mem_insert _ _)
    have hTV : T₂ ∈ fr.V T₂ := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    have hcJ : c ∈ Subgroup.centralizer ({J} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hc J hJV).symm
    have hcT : T₂ * c = c * T₂ := Subgroup.mem_centralizer_iff.mp hc T₂ hTV
    have hnorm := K₀_normal hL Z e hZc hZo hJ hJ2
    refine JT.mem_normalizer_of_conj_mem fun y hy => ?_
    rw [mem_A_iff hL Z e hq hR1 hZc hZo hM hJ hJ2 fr hT hT2] at hy ⊢
    obtain ⟨hyKC, hodd⟩ := hy
    have hyK := (Subgroup.mem_inf.mp hyKC).1
    have hyT := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hyKC).2
    refine ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · have := hnorm.conj_mem ⟨y, (hyp hL Z e hq hR1 hZc hZo hM J hJ hJ2).le_centralizer hyK⟩
        (Subgroup.mem_subgroupOf.mpr hyK) ⟨c, hcJ⟩
      exact Subgroup.mem_subgroupOf.mp this
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hcT' : c⁻¹ * T₂ = T₂ * c⁻¹ := by
        calc c⁻¹ * T₂ = c⁻¹ * (T₂ * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * T₂) * c⁻¹ := by rw [hcT]
          _ = T₂ * c⁻¹ := by group
      calc c * y * c⁻¹ * T₂ = c * y * (c⁻¹ * T₂) := by group
        _ = c * y * (T₂ * c⁻¹) := by rw [hcT']
        _ = c * (y * T₂) * c⁻¹ := by group
        _ = c * (T₂ * y) * c⁻¹ := by rw [hyT]
        _ = (c * T₂) * y * c⁻¹ := by group
        _ = (T₂ * c) * y * c⁻¹ := by rw [← hcT]
        _ = T₂ * (c * y * c⁻¹) := by group
    · rwa [orderOf_conj_mul]
  have hUA : U ≤ Subgroup.normalizer (fr.A T₂ : Set G) := by
    intro u hu
    have huV : u ∈ Subgroup.normalizer (fr.V T₂ : Set G) := by
      rw [hNV]; exact Subgroup.mem_sup_left hu
    have huL : proj Z e u ∈ Subgroup.normalizer (AL : Set L) := by
      have := Subgroup.le_normalizer_map (proj Z e) ⟨u, huV, rfl⟩
      rwa [hmapV, hNVA] at this
    have hAE : fr.A T₂ ⊔ fr.E = AL.comap (proj Z e) := by
      rw [hE, hAL, ← hmapA, Subgroup.comap_map_eq, ker_proj]
    have huAE : u ∈ Subgroup.normalizer ((fr.A T₂ ⊔ fr.E : Subgroup G) : Set G) := by
      rw [hAE]; exact Subgroup.le_normalizer_comap (proj Z e) huL
    have hmapT₁ : ((fr.S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G)).map
        (MulAut.conj u).toMonoidHom = (fr.S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have : u * y * u⁻¹ = y := by
          rw [Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 u hu]; group
        show u * y * u⁻¹ ∈ _
        rw [this]
        exact hy
      · intro hx
        refine ⟨x, hx, ?_⟩
        have : u * x * u⁻¹ = x := by
          rw [Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 u hu]; group
        exact this
    have hmapA' : (fr.A T₂).map (MulAut.conj u).toMonoidHom = fr.A T₂ := by
      conv_lhs => rw [← hT1A]
      rw [Subgroup.map_commutator, hmapT₁, map_conj_eq_of_mem_normalizer huAE, hT1A]
    refine JT.mem_normalizer_of_conj_mem fun y hy => ?_
    have : u * y * u⁻¹ ∈ (fr.A T₂).map (MulAut.conj u).toMonoidHom :=
      ⟨y, hy, by simp [MulAut.conj_apply]⟩
    rwa [hmapA'] at this
  have hNVA' : Subgroup.normalizer (fr.V T₂ : Set G) ≤ Subgroup.normalizer (fr.A T₂ : Set G) := by
    rw [hNV]; exact sup_le hUA hCVA
  have hNAα : ∀ Aα : Subgroup G, Aα ≤ fr.A T₂ →
      Subgroup.normalizer (fr.A T₂ : Set G) ≤ Subgroup.normalizer (Aα : Set G) := by
    intro Aα hle g hg
    refine JT.mem_normalizer_of_conj_mem fun y hy => ?_
    set B := Aα.map (MulAut.conj g).toMonoidHom with hB
    have hBA : B ≤ fr.A T₂ := by
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg x).mp (hle hx)
    have hcard : Nat.card B = Nat.card Aα :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have heq : B.subgroupOf (fr.A T₂) = Aα.subgroupOf (fr.A T₂) := by
      rw [IsCyclic.subgroup_eq_iff_card_eq,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard]
    have hyB : g * y * g⁻¹ ∈ B := ⟨y, hy, by simp [MulAut.conj_apply]⟩
    have : (⟨g * y * g⁻¹, hBA hyB⟩ : fr.A T₂) ∈ B.subgroupOf (fr.A T₂) := hyB
    rw [heq] at this
    exact this
  have hG3c : ∀ Aα : Subgroup G, Aα ≤ fr.A T₂ → Aα ≠ ⊥ →
      Subgroup.normalizer (Aα : Set G) = Subgroup.normalizer (fr.V T₂ : Set G) := by
    intro Aα hle hne
    obtain ⟨a, haA, ha1, hmap⟩ := hgen Aα hle hne
    apply le_antisymm
    · intro g hg
      have h1 : proj Z e g ∈ Subgroup.normalizer ((Aα.map (proj Z e) : Subgroup L) : Set L) :=
        Subgroup.le_normalizer_map (proj Z e) ⟨g, hg, rfl⟩
      rw [hmap, (hCa a haA ha1).2, ← hNVA, ← hmapV] at h1
      exact mem_normalizer_of_map Z e hZc hZo hV2 h1
    · exact hNVA'.trans (hNAα Aα hle)
  obtain ⟨gA, hgA⟩ := exists_eq_zpowers (fr.A T₂)
  have hAcomm : ∀ x ∈ fr.A T₂, ∀ y ∈ fr.A T₂, x * y = y * x := by
    intro x hx y hy
    rw [hgA] at hx hy
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨n, rfl⟩ := hy
    exact (Commute.zpow_zpow_self gA m n).eq
  have hG3c' : ∀ Aα : Subgroup G, Aα ≤ fr.A₀ T₂ → Aα ≠ ⊥ →
      Subgroup.centralizer (Aα : Set G) = fr.V T₂ ⊔ fr.A T₂ ⊔ fr.E := by
    intro Aα hle hne
    have hleA : Aα ≤ fr.A T₂ := hle.trans inf_le_left
    obtain ⟨a, haA, ha1, hmap⟩ := hgen Aα hleA hne
    apply le_antisymm
    · intro g hg
      have h1 : proj Z e g ∈ Subgroup.centralizer ((Aα.map (proj Z e) : Subgroup L) : Set L) := by
        have := Subgroup.map_centralizer_le_centralizer_image (Aα : Set G) (proj Z e)
          ⟨g, hg, rfl⟩
        rwa [← Subgroup.coe_map] at this
      rw [hmap, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, (hCa a haA ha1).1,
        ← hmapV, hAL, ← hmapA, ← Subgroup.map_sup] at h1
      have := Subgroup.mem_comap.mpr h1
      rw [hE]
      rwa [Subgroup.comap_map_eq, ker_proj] at this
    · refine sup_le (sup_le ?_ ?_) ?_
      · change Subgroup.closure {J, T₂} ≤ _
        rw [Subgroup.closure_le]
        rintro x (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] <;>
          intro y hy
        · have hyK := A_le_K₀ hL Z e hq hR1 hZc hZo hM hJ hJ2 fr (hleA hy)
          exact Subgroup.mem_centralizer_singleton_iff.mp
            (K₀_le_centralizer hL Z e hq hR1 hZc hZo hM hJ hyK)
        · have hyT := (Subgroup.mem_inf.mp (oddPart_le _ (hleA hy))).2
          exact Subgroup.mem_centralizer_singleton_iff.mp hyT
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact hAcomm y (hleA hy) x hx
      · intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        rw [hE] at hz
        exact Subgroup.mem_center_iff.mp (hZc hz) y
  have hG4 : fr.A₀ T₂ ≠ ⊥ := by
    intro hbot
    have hA : fr.A T₂ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : x ∈ fr.A₀ T₂ := by
        refine ⟨hx, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
        rw [hE] at hz
        exact (Subgroup.mem_center_iff.mp (hZc hz) x).symm
      rwa [hbot] at this
    have h1 := card_map_A hL Z e hq hR1 hZc hZo hM hJ hJ2 fr (T₂ := T₂)
    rw [hmapA, hA, Subgroup.card_bot] at h1
    rw [h1] at hcardA
    change 4 * 1 = hL.p ^ hL.f + 1 at hcardA
    have : hL.q = 3 := by change hL.p ^ hL.f = 3; omega
    omega
  let hI : HypI G :=
    { toHyp := hyp hL Z e hq hR1 hZc hZo hM J hJ hJ2
      fr := fr
      p_eq_three := hp3
      odd_f := hfodd
      one_lt_f := hf1
      perfect := hperf
      cover := lemma_2_6_cover G _ fr hidx }
  exact ⟨{ toHypI := hI
           T₂ := T₂
           T₂_mem := hT
           T₂_order := hT2
           U := U
           card_U := hU3
           G3a := hNV
           G3a' := ⟨hUE, hUV⟩
           G3b := hCV
           G3c := hG3c
           G3c' := hG3c'
           G4 := hG4 }, hE⟩

end CFSG.Walter.W67
