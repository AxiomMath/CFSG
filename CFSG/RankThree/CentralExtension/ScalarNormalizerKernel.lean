module

public import CFSG.RankThree.CentralExtension.CentralKernelTools
public import CFSG.RankThree.CentralExtension.ScalarComplement

public section

namespace CFSG.RankThree.CentralExtension

open Subgroup
open scoped commutatorElement

universe u

section Framework

variable {E : Type*} [Group E] {p : ℕ} [hp : Fact p.Prime]

theorem exists_sylow_le_of_index_coprime [Finite E] (L : Subgroup E) (hL : L.index.Coprime p) :
    ∃ T : Sylow p E, (T : Subgroup E) ≤ L := by
  let P : Sylow p L := default
  have hcard : Nat.card ((P : Subgroup L).map L.subtype) = p ^ (Nat.card E).factorization p := by
    rw [card_map_of_injective L.subtype_injective, P.card_eq_multiplicity]
    congr 1
    have h1 := L.card_mul_index
    have hLpos : Nat.card L ≠ 0 := Nat.card_pos.ne'
    have hipos : L.index ≠ 0 := index_ne_zero_of_finite
    have hnd : ¬ p ∣ L.index := (Nat.Prime.coprime_iff_not_dvd hp.out).1 hL.symm
    rw [← h1, Nat.factorization_mul hLpos hipos, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]
  exact ⟨Sylow.ofCard _ hcard, by rw [Sylow.coe_ofCard]; exact map_subtype_le _⟩

theorem pKernel_eq_bot_of_normalized_complement [Finite E] [Group.IsPerfect E] {S : Type*}
    [Group S] (π : E →* S) (hC : π.ker ≤ center E) (hCp : IsPGroup p π.ker) {H Q : Subgroup S}
    [(Q.subgroupOf H).Normal]
    (hcyc : ∀ P : Sylow p (H ⧸ Q.subgroupOf H), IsCyclic P) (hL : (H.comap π).index.Coprime p)
    (D : Subgroup E) (hDU : D ≤ Q.comap π) (hCD : π.ker ⊓ D = ⊥)
    (hCU : ∀ u ∈ Q.comap π, ∃ c ∈ π.ker, c⁻¹ * u ∈ D)
    (hLD : ∀ g ∈ H.comap π, ∀ d ∈ D, g * d * g⁻¹ ∈ D) : π.ker = ⊥ := by
  obtain ⟨T, hTL⟩ := exists_sylow_le_of_index_coprime (H.comap π) hL
  let f : (T : Subgroup E) →* H ⧸ Q.subgroupOf H :=
    (QuotientGroup.mk' _).comp ((π.subgroupComap H).comp (inclusion hTL))
  have hf : ∀ t : (T : Subgroup E), f t = 1 ↔ (t : E) ∈ Q.comap π := fun t => by
    change (QuotientGroup.mk (π.subgroupComap H (inclusion hTL t)) : H ⧸ Q.subgroupOf H) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
    rfl
  have : IsCyclic f.range := isCyclic_range_of_isPGroup T.isPGroup' hcyc f
  exact eq_bot_of_complement_of_cyclic_quotient hC hCp hCU hCD T
    (fun g hg d hd => hLD g (hTL hg) d hd) f (fun t ht => (hf t).1 ht)
    (fun t ht => (hf t).2 (hDU ht))

end Framework

variable {p : ℕ} [hp : Fact p.Prime] {S : Type*} [Group S]

theorem scalar_normalizer_pKernel_eq_bot [Finite S] {H Q : Subgroup S} (hHp : H.index.Coprime p)
    (hQH : Q ≤ H) [(Q.subgroupOf H).Normal] (hQexp : ∀ q ∈ Q, q ^ p = 1)
    (hZQ : center Q = commutator Q) (hZcard : Nat.card (center Q) = p)
    (hcyc : ∀ P : Sylow p (H ⧸ Q.subgroupOf H), IsCyclic P) (σ : H ⧸ Q.subgroupOf H)
    (hσZ : σ ∈ center (H ⧸ Q.subgroupOf H)) (hσo : (orderOf σ).Coprime p) (r : ZMod p)
    (hr2 : r ^ 2 ≠ 1) (hr3 : r ^ 3 ≠ 1)
    (hσV : ∀ h : H, (h : H ⧸ Q.subgroupOf H) = σ → ∀ q ∈ Q,
      ((h : S) * q * (h : S)⁻¹)⁻¹ * q ^ r.val ∈ (center Q).map Q.subtype)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* S)
    (hπ : Function.Surjective π) (hC : π.ker ≤ center E) (hCp : IsPGroup p π.ker) :
    π.ker = ⊥ := by
  classical
  have hQexp' : ∀ q : Q, q ^ p = 1 := fun q => Subtype.ext (by simpa using hQexp q q.2)
  have hQp : IsPGroup p Q := fun q => ⟨1, by rw [pow_one]; exact hQexp' q⟩
  set L : Subgroup E := H.comap π with hLdef
  set U : Subgroup E := Q.comap π with hUdef
  have hUp : IsPGroup p U := hQp.comap_of_ker_isPGroup π hCp
  have hQnorm : ∀ q ∈ Q, ∀ h ∈ H, h * q * h⁻¹ ∈ Q := fun q hq h hh =>
    (normal_subgroupOf_iff hQH).1 inferInstance q h hq hh
  have hLnorm : ∀ g ∈ L, g ∈ normalizer (U : Set E) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      rw [hUdef, mem_comap, map_mul, map_mul, map_inv]
      exact hQnorm _ hu _ hg
    · intro hu
      have h1 := hQnorm _ hu _ (H.inv_mem (show π g ∈ H from hg))
      rw [map_mul, map_mul, map_inv, inv_inv,
        show (π g)⁻¹ * (π g * π u * (π g)⁻¹) * π g = π u by group] at h1
      exact h1
  let ρ : L →* H ⧸ Q.subgroupOf H := (QuotientGroup.mk' _).comp (π.subgroupComap H)
  have hρsurj : Function.Surjective ρ := by
    intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨e, he⟩ := hπ h
    refine ⟨⟨e, by rw [hLdef, mem_comap, he]; exact h.2⟩, ?_⟩
    change (QuotientGroup.mk (π.subgroupComap H _) : H ⧸ Q.subgroupOf H) = _
    congr 1
    exact Subtype.ext he
  have hρU : ∀ x : L, ρ x = 1 ↔ (x : E) ∈ U := fun x => by
    change (QuotientGroup.mk (π.subgroupComap H x) : H ⧸ Q.subgroupOf H) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
    rfl
  obtain ⟨y, hy⟩ := hρsurj σ
  set m := orderOf σ with hmdef
  have hm0 : 0 < m := orderOf_pos σ
  have : NeZero m := ⟨hm0.ne'⟩
  have hym : ((y ^ m : L) : E) ∈ U := (hρU _).1 (by rw [map_pow, hy, pow_orderOf_eq_one])
  obtain ⟨a, ha⟩ := hUp ⟨_, hym⟩
  have ha' : (y ^ m) ^ p ^ a = 1 := Subtype.ext (by simpa using congrArg Subtype.val ha)
  have hcop : (p ^ a).Coprime m := (hσo.pow_right a).symm
  set e := (((ZMod.unitOfCoprime (p ^ a) hcop)⁻¹ : (ZMod m)ˣ) : ZMod m).val with hedef
  have he : ((p ^ a * e : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m) := by
    rw [Nat.cast_mul, hedef, ZMod.natCast_zmod_val, ← ZMod.coe_unitOfCoprime (p ^ a) hcop,
      Units.mul_inv, Nat.cast_one]
  have hmod : p ^ a * e ≡ 1 [MOD m] := (ZMod.natCast_eq_natCast_iff _ _ _).1 he
  set t : L := y ^ (p ^ a * e) with htdef
  have htm : t ^ m = 1 := by
    rw [htdef, ← pow_mul, show p ^ a * e * m = m * p ^ a * e by ring, pow_mul, pow_mul, ha',
      one_pow]
  have hρt : ρ t = σ := by
    rw [htdef, map_pow, hy]
    nth_rewrite 2 [← pow_one σ]
    rw [pow_eq_pow_iff_modEq]
    exact hmod
  have htN : (t : E) ∈ normalizer (U : Set E) := hLnorm _ t.2
  set α : MulAut U := U.normalizerMonoidHom ⟨(t : E), htN⟩ with hα
  have hαapp : ∀ u : U, (α u : E) = t * u * (t : E)⁻¹ := fun _ => rfl
  have hαo : (orderOf α).Coprime p := by
    have h1 : orderOf α ∣ orderOf (⟨(t : E), htN⟩ : normalizer (U : Set E)) :=
      orderOf_map_dvd _ _
    have h2 : orderOf (⟨(t : E), htN⟩ : normalizer (U : Set E)) ∣ m :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using congrArg Subtype.val htm))
    exact Nat.Coprime.coprime_dvd_left (h1.trans h2) hσo
  let πU : U →* Q := π.subgroupComap Q
  have hπU : ∀ u : U, (πU u : S) = π u := fun _ => rfl
  have hπUsurj : Function.Surjective πU := fun q => by
    obtain ⟨e, he⟩ := hπ q
    exact ⟨⟨e, by rw [hUdef, mem_comap, he]; exact q.2⟩, Subtype.ext he⟩
  have hπUker : ∀ u : U, u ∈ πU.ker ↔ (u : E) ∈ π.ker := fun u => by
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← hπU, OneMemClass.coe_eq_one]
  have hCU : πU.ker ≤ center U := fun u hu =>
    mem_center_iff.2 fun g => Subtype.ext (mem_center_iff.1 (hC ((hπUker u).1 hu)) g)
  have hCpU : IsPGroup p πU.ker := by
    intro c
    obtain ⟨k, hk⟩ := hCp ⟨(c : E), (hπUker c).1 c.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have hαC : ∀ c ∈ πU.ker, α c = c := fun c hc => Subtype.ext (by
    rw [hαapp, mem_center_iff.1 (hC ((hπUker c).1 hc)) (t : E), mul_inv_cancel_right])
  have hαV : ∀ u : U, (QuotientGroup.mk (πU (α u)) : Q ⧸ center Q) =
      (QuotientGroup.mk (πU u)) ^ r.val := by
    intro u
    rw [mk_eq_pow_iff_mem_center]
    have hh : ((⟨π t, t.2⟩ : H) : H ⧸ Q.subgroupOf H) = σ := hρt
    have h1 := hσV ⟨π t, t.2⟩ hh (π u) u.2
    obtain ⟨z, hz, hzeq⟩ := h1
    have hz2 : (z : S) = (π t * π u * (π t)⁻¹)⁻¹ * π u ^ r.val := hzeq
    have hz' : (πU u ^ r.val)⁻¹ * πU (α u) = z⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, SubgroupClass.coe_pow, hπU, hαapp,
        map_mul, map_inv]
      rw [hz2]
      group
    rw [hz']
    exact inv_mem hz
  obtain ⟨-, D₀, ⟨hinv, hsup, hinf⟩, huniq, -, hD₀norm, -, -⟩ :=
    extraspecial_scalar_central_extension_unique_complement πU hπUsurj hCU hCpU hQexp' hZQ
      hZcard α hαo hαC r hr2 hr3 hαV
  have hconjD : ∀ g (hg : g ∈ L), ∀ d ∈ D₀, U.normalizerMonoidHom ⟨g, hLnorm g hg⟩ d ∈ D₀ := by
    intro g hg
    set φ : MulAut U := U.normalizerMonoidHom ⟨g, hLnorm g hg⟩ with hφ
    have hφapp : ∀ u : U, (φ u : E) = g * u * g⁻¹ := fun _ => rfl
    have hφC : ∀ c ∈ πU.ker, φ c = c := fun c hc => Subtype.ext (by
      rw [hφapp, mem_center_iff.1 (hC ((hπUker c).1 hc)) g, mul_inv_cancel_right])
    have hkerφ : πU.ker.map φ.toMonoidHom = πU.ker := by
      ext x
      constructor
      · rintro ⟨c, hc, rfl⟩
        change φ c ∈ πU.ker
        rw [hφC c hc]
        exact hc
      · intro hx
        exact ⟨x, hx, hφC x hx⟩
    have hsupg : πU.ker ⊔ D₀.map φ.toMonoidHom = ⊤ := by
      rw [← hkerφ, ← Subgroup.map_sup, hsup, map_top_of_surjective φ.toMonoidHom φ.surjective]
    have hinfg : πU.ker ⊓ D₀.map φ.toMonoidHom = ⊥ := by
      rw [← hkerφ, ← Subgroup.map_inf_eq _ _ φ.toMonoidHom φ.injective, hinf, Subgroup.map_bot]
    have hinvg : ∀ x ∈ D₀.map φ.toMonoidHom, α x ∈ D₀.map φ.toMonoidHom := by
      rintro _ ⟨d, hd, rfl⟩
      have hu₀ : (t : E)⁻¹ * (g⁻¹ * t * g) ∈ U := by
        have h1 : ρ (t⁻¹ * ((⟨g, hg⟩ : L)⁻¹ * t * ⟨g, hg⟩)) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, hρt,
            mem_center_iff.1 hσZ (ρ ⟨g, hg⟩)⁻¹]
          group
        exact (hρU _).1 h1
      refine ⟨α (⟨_, hu₀⟩ * d * (⟨_, hu₀⟩ : U)⁻¹),
        hinv _ (hD₀norm.conj_mem d hd ⟨_, hu₀⟩), ?_⟩
      apply Subtype.ext
      change (φ (α (⟨_, hu₀⟩ * d * (⟨_, hu₀⟩ : U)⁻¹)) : E) = (α (φ d) : E)
      rw [hφapp, hαapp, hαapp, hφapp]
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group
    have hDg := huniq _ hinvg hsupg hinfg
    intro d hd
    rw [← hDg]
    exact ⟨d, hd, rfl⟩
  set D : Subgroup E := D₀.map U.subtype with hDdef
  have hDU : D ≤ U := map_subtype_le D₀
  have hLD : ∀ g ∈ L, ∀ x ∈ D, g * x * g⁻¹ ∈ D := by
    rintro g hg _ ⟨d, hd, rfl⟩
    exact ⟨_, hconjD g hg d hd, rfl⟩
  have hCU' : ∀ u ∈ U, ∃ c ∈ π.ker, c⁻¹ * u ∈ D := by
    intro u hu
    have hu' : (⟨u, hu⟩ : U) ∈ πU.ker ⊔ D₀ := by rw [hsup]; exact mem_top _
    have : πU.ker.Normal := inferInstance
    obtain ⟨c, hc, d, hd, hcd⟩ := mem_sup_of_normal_left.1 hu'
    refine ⟨c, (hπUker c).1 hc, d, hd, ?_⟩
    have h1 := congrArg Subtype.val hcd
    simp only [Subgroup.coe_mul] at h1
    rw [coe_subtype, ← h1, inv_mul_cancel_left]
  have hCD : π.ker ⊓ D = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxC, d, hd, rfl⟩ := hx
    have h1 : d ∈ πU.ker ⊓ D₀ := ⟨(hπUker d).2 hxC, hd⟩
    rw [hinf, mem_bot] at h1
    rw [h1]
    exact one_mem _
  have hLp : L.index.Coprime p := by rw [hLdef, index_comap_of_surjective H hπ]; exact hHp
  exact pKernel_eq_bot_of_normalized_complement π hC hCp hcyc hLp D hDU hCD hCU' hLD

theorem central_cover_extraspecial_scalar_normalizer_kernel_trivial [Finite S]
    {H Q : Subgroup S} (hHp : H.index.Coprime p) (hQH : Q ≤ H) [(Q.subgroupOf H).Normal]
    (hQexp : ∀ q ∈ Q, q ^ p = 1) (hZQ : center Q = commutator Q)
    (hZcard : Nat.card (center Q) = p) (hcyc : ∀ P : Sylow p (H ⧸ Q.subgroupOf H), IsCyclic P)
    (σ : H ⧸ Q.subgroupOf H) (hσZ : σ ∈ center (H ⧸ Q.subgroupOf H))
    (hσo : (orderOf σ).Coprime p) (r : ZMod p) (hr2 : r ^ 2 ≠ 1) (hr3 : r ^ 3 ≠ 1)
    (hσV : ∀ h : H, (h : H ⧸ Q.subgroupOf H) = σ → ∀ q ∈ Q,
      ((h : S) * q * (h : S)⁻¹)⁻¹ * q ^ r.val ∈ (center Q).map Q.subtype)
    {E : Type u} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* S)
    (hπ : Function.Surjective π) (hC : π.ker ≤ center E) (Cp : Sylow p π.ker) :
    (Cp : Subgroup π.ker) = ⊥ :=
  sylow_ker_eq_bot_of_pKernel π hπ hC
    (fun _ _ _ _ π' hπ' hC' hCp' => scalar_normalizer_pKernel_eq_bot hHp hQH hQexp hZQ hZcard
      hcyc σ hσZ hσo r hr2 hr3 hσV π' hπ' hC' hCp') Cp

end CFSG.RankThree.CentralExtension
