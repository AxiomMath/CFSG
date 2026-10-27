module

public import CFSG.Quasithin.Vol2.Ch3E215MSp4B

public section

namespace CFSG.Quasithin.Ch3E215M.Sp4

variable {G : Type} [Group G] {P Z : Subgroup G}

theorem normal_subgroupOf (hZP : Z ≤ P) (hc : ∀ z ∈ Z, ∀ p ∈ P, p * z * p⁻¹ = z) :
    (Z.subgroupOf P).Normal :=
  (Subgroup.normal_subgroupOf_iff hZP).2 fun z p hz hp => by rw [hc z hz p hp]; exact hz

theorem map_normalizerMonoidHom {l : G} (hlP : l ∈ Subgroup.normalizer (P : Set G))
    (hlZ : l ∈ Subgroup.normalizer (Z : Set G)) :
    (Z.subgroupOf P).map (P.normalizerMonoidHom ⟨l, hlP⟩ : ↥P →* ↥P) = Z.subgroupOf P := by
  ext q
  constructor
  · rintro ⟨q', hq', rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hq'
    rw [Subgroup.mem_subgroupOf]
    exact (hlZ _).mp hq'
  · intro hq
    rw [Subgroup.mem_subgroupOf] at hq
    have hq1 : l⁻¹ * (q : G) * l ∈ P := by
      have := (Subgroup.inv_mem _ hlP (q : G)).mp q.2
      simpa using this
    refine ⟨⟨l⁻¹ * q * l, hq1⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      have := (Subgroup.inv_mem _ hlZ (q : G)).mp hq
      simpa using this
    · apply Subtype.ext
      show l * (l⁻¹ * (q : G) * l) * l⁻¹ = q
      group

variable [(Z.subgroupOf P).Normal]

@[expose, reducible] def quotCommGroup (hcomm : ∀ p ∈ P, ∀ q ∈ P, p * q * p⁻¹ * q⁻¹ ∈ Z) :
    CommGroup (↥P ⧸ Z.subgroupOf P) :=
  { (inferInstance : Group (↥P ⧸ Z.subgroupOf P)) with
    mul_comm := fun a b => by
      obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have h := hcomm _ (P.inv_mem q.2) _ (P.inv_mem p.2)
      have e : (((p * q)⁻¹ * (q * p) : ↥P) : G) =
          (q : G)⁻¹ * (p : G)⁻¹ * ((q : G)⁻¹)⁻¹ * ((p : G)⁻¹)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]
      rw [e]
      exact h }

@[expose] noncomputable def conjQ {l : G} (hlP : l ∈ Subgroup.normalizer (P : Set G))
    (hlZ : l ∈ Subgroup.normalizer (Z : Set G)) : MulAut (↥P ⧸ Z.subgroupOf P) :=
  QuotientGroup.congr (Z.subgroupOf P) (Z.subgroupOf P) (P.normalizerMonoidHom ⟨l, hlP⟩)
    (map_normalizerMonoidHom hlP hlZ)

theorem conjQ_mk {l : G} (hlP : l ∈ Subgroup.normalizer (P : Set G))
    (hlZ : l ∈ Subgroup.normalizer (Z : Set G)) (p : ↥P) :
    conjQ hlP hlZ (p : ↥P ⧸ Z.subgroupOf P) =
      ((⟨l * p * l⁻¹, (hlP p).mp p.2⟩ : ↥P) : ↥P ⧸ Z.subgroupOf P) :=
  rfl

@[expose] noncomputable def actQ {L : Subgroup G} (hLP : L ≤ Subgroup.normalizer (P : Set G))
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G)) : ↥L →* MulAut (↥P ⧸ Z.subgroupOf P) where
  toFun l := conjQ (hLP l.2) (hLZ l.2)
  map_one' := by
    ext q
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective q
    rw [conjQ_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    show (1 : G) * p * 1⁻¹ = p
    group
  map_mul' a b := by
    ext q
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MulAut.mul_apply, conjQ_mk, conjQ_mk, conjQ_mk]
    congr 1
    apply Subtype.ext
    show (a : G) * b * p * ((a : G) * b)⁻¹ = a * (b * p * (b : G)⁻¹) * (a : G)⁻¹
    group

theorem actQ_mk {L : Subgroup G} (hLP : L ≤ Subgroup.normalizer (P : Set G))
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G)) (l : ↥L) (p : ↥P) :
    actQ hLP hLZ l (p : ↥P ⧸ Z.subgroupOf P) =
      ((⟨l * p * (l : G)⁻¹, (hLP l.2 p).mp p.2⟩ : ↥P) : ↥P ⧸ Z.subgroupOf P) :=
  rfl

@[expose] def comapQ (Y : Subgroup (↥P ⧸ Z.subgroupOf P)) : Subgroup G :=
  (Y.comap (QuotientGroup.mk' (Z.subgroupOf P))).map P.subtype

theorem mem_comapQ {Y : Subgroup (↥P ⧸ Z.subgroupOf P)} {x : G} :
    x ∈ comapQ Y ↔ ∃ hx : x ∈ P, ((⟨x, hx⟩ : ↥P) : ↥P ⧸ Z.subgroupOf P) ∈ Y := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, hp⟩
  · rintro ⟨hx, hY⟩
    exact ⟨⟨x, hx⟩, hY, rfl⟩

theorem comapQ_le (Y : Subgroup (↥P ⧸ Z.subgroupOf P)) : comapQ Y ≤ P := by
  rintro _ ⟨p, -, rfl⟩
  exact p.2

theorem le_comapQ (hZP : Z ≤ P) (Y : Subgroup (↥P ⧸ Z.subgroupOf P)) : Z ≤ comapQ Y := by
  intro z hz
  refine mem_comapQ.2 ⟨hZP hz, ?_⟩
  rw [(QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hz)]
  exact Y.one_mem

theorem le_normalizer_comapQ {L : Subgroup G} (hLP : L ≤ Subgroup.normalizer (P : Set G))
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G)) {Y : Subgroup (↥P ⧸ Z.subgroupOf P)}
    (hY : ∀ l : ↥L, ∀ q ∈ Y, actQ hLP hLZ l q ∈ Y) :
    L ≤ Subgroup.normalizer (comapQ Y : Set G) := by
  intro l hl
  have key : ∀ m : G, ∀ hm : m ∈ L, ∀ x ∈ comapQ Y, m * x * m⁻¹ ∈ comapQ Y := by
    intro m hm x hx
    obtain ⟨hxP, hxY⟩ := mem_comapQ.1 hx
    refine mem_comapQ.2 ⟨(hLP hm x).mp hxP, ?_⟩
    have := hY ⟨m, hm⟩ _ hxY
    rwa [actQ_mk] at this
  intro x
  constructor
  · exact key l hl x
  · intro hx
    have := key l⁻¹ (L.inv_mem hl) _ hx
    simpa [mul_assoc] using this

end CFSG.Quasithin.Ch3E215M.Sp4
