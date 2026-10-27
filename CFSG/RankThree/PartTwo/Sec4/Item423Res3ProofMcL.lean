module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofSporAll
public import CFSG.RankThree.PartTwo.Sec21.ThreeLocalSporProofMcL

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open Subgroup

namespace Res423Three

open Res423Two

theorem core_eq_bot_of_isCharacteristicP {C : Type*} [Group C] [Finite C]
    (h : IsCharacteristicP 3 C) : aschbacherSolvableCore 3 C = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hchar, hN3, -⟩ :=
    solvable_prime_complement_core_characterization (H := C) Nat.prime_three
  set N := aschbacherSolvableCore 3 C with hNdef
  have : N.Characteristic := hchar
  have : N.Normal := inferInstance
  have : (CFSG.pCore 3 C).Normal := CFSG.pCore_normal
  have hdisj : N ⊓ CFSG.pCore 3 C = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 3) (G := C))
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3).symm
  have hcomm : ⁅N, CFSG.pCore 3 C⁆ = ⊥ := le_bot_iff.mp (hdisj ▸ Subgroup.commutator_le_inf _ _)
  have hle : N ≤ CFSG.pCore 3 C :=
    ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm).trans h
  rw [eq_bot_iff, ← hdisj]
  exact le_inf le_rfl hle

theorem exists_pow_eq_one_of_mem_center {C : Type*} [Group C] (h : IsCharacteristicP 3 C)
    {c : C} (hc : c ∈ Subgroup.center C) : ∃ k : ℕ, c ^ 3 ^ k = 1 := by
  have hcO : c ∈ CFSG.pCore 3 C :=
    h (Subgroup.center_le_centralizer (CFSG.pCore 3 C : Set C) hc)
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 3) (G := C) ⟨c, hcO⟩
  exact ⟨k, congrArg Subtype.val hk⟩

theorem alphaVanishes_of_rigid {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    {D : Subgroup X} (hD : D ≠ ⊥)
    (hθ : ∀ b ∈ D, b ≠ 1 → aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set X)) = ⊥)
    (hrig : ∀ b ∈ D, b ≠ 1 → ∀ σ : MulAut X, Nat.Coprime (orderOf σ) 3 →
      (∀ c ∈ Subgroup.centralizer ({b} : Set X), σ c = c) → σ = 1) :
    AlphaVanishes X D := by
  intro Y hY
  refine thetaAlpha_eq_bot_of_forall (subgroupOf_ne_bot hZ hD hY) fun b hb hb1 => ?_
  obtain ⟨b₀, hb₀, hbb₀⟩ := Subgroup.mem_subgroupOf.mp hb
  have hb₀1 : b₀ ≠ 1 := by
    rintro rfl
    apply hb1
    apply Subtype.ext
    rw [← hbb₀]
    simp
  rw [eq_bot_iff]
  intro q hq
  rw [Subgroup.mem_bot]
  have hfix : ∀ c ∈ Subgroup.centralizer ({b₀} : Set X), (q : MulAut X) c = c := fun c hc =>
    fix_of_mem_theta hZ hY (hθ b₀ hb₀ hb₀1) hbb₀.symm hq hc
  have hcop : Nat.Coprime (orderOf (q : MulAut X)) 3 := by
    rw [Subgroup.orderOf_coe]
    have h1 : orderOf (⟨q, hq⟩ : inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({b} : Set Y))) ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3)
          (Subgroup.centralizer ({b} : Set Y))) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Nat.Coprime.coprime_dvd_left h1
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        (not_three_dvd_card_inSubgroup_theta _)).symm
  exact Subtype.ext (hrig b₀ hb₀ hb₀1 _ hcop hfix)

section McL

open CFSG.Sporadic.Schreier (mclP)
open CFSG.Sporadic.SmallOddCore (mclR mclRows tp)
open CFSG.RankThree.PartTwo.Sec6.ThreeLocalSporProof


theorem card_centralizer_mclP (z : mclP) (hz : orderOf z = 3) :
    Nat.card (Subgroup.centralizer ({z} : Set mclP)) = 29160 ∨
      Nat.card (Subgroup.centralizer ({z} : Set mclP)) = 972 := by
  obtain ⟨ht₁, ht₂, -, -, c₁, c₂, -, -, -, hall⟩ :=
    CFSG.Sporadic.Recognition.McLAS.mclP_order_three_classes
      CFSG.Sporadic.Recognition.McLAS.threeFacts_cert
  have hz3 : orderOf (z : Equiv.Perm (Fin 275)) = 3 := by rw [Subgroup.orderOf_coe, hz]
  rcases hall z z.2 hz3 with ⟨g, hg, hzg⟩ | ⟨g, hg, hzg⟩
  · left
    rw [Sec6.ThreeLocalSporProof.card_centralizer_of_isConj
        (isConj_of_eq_conj (t := ⟨_, ht₁⟩) hg hzg),
      card_centralizer_singleton (⟨_, ht₁⟩ : mclP), c₁]
  · right
    rw [Sec6.ThreeLocalSporProof.card_centralizer_of_isConj
        (isConj_of_eq_conj (t := ⟨_, ht₂⟩) hg hzg),
      card_centralizer_singleton (⟨_, ht₂⟩ : mclP), c₂]

theorem center_mclP_eq_bot : Subgroup.center mclP = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hC := CFSG.Sporadic.SmallOddCore.mcl_centralizer_eq_bot
  have hzC : (z : Equiv.Perm (Fin 275)) ∈
      Subgroup.centralizer (mclP : Set (Equiv.Perm (Fin 275))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨p, hp⟩)
  rw [hC, Subgroup.mem_bot] at hzC
  exact Subtype.ext hzC

theorem eq_one_of_fix_mclP (z : mclP) (hz : orderOf z = 3) (σ : MulAut mclP)
    (hσ : Nat.Coprime (orderOf σ) 3)
    (hfix : ∀ c ∈ Subgroup.centralizer ({z} : Set mclP), σ c = c) : σ = 1 := by
  obtain ⟨e, he, -, -, -⟩ := CFSG.Sporadic.SmallOddCore.mcl_full_automorphism_model
  obtain ⟨x, rfl⟩ : ∃ x : mclR, σ = e x := ⟨e.symm σ, (e.apply_symm_apply σ).symm⟩
  have hxc : ∀ c ∈ Subgroup.centralizer ({z} : Set mclP),
      (x : Equiv.Perm (Fin 275)) * c = c * x := by
    intro c hc
    have h1 := he x c
    rw [hfix c hc, Subgroup.coe_inv] at h1
    calc (x : Equiv.Perm (Fin 275)) * c = (x * c * (x : Equiv.Perm (Fin 275))⁻¹) * x := by
          group
      _ = c * x := by rw [← h1]
  have hox : orderOf x = orderOf (e x) := (MulEquiv.orderOf_eq e x).symm
  obtain ⟨-, -, -, -, -, hRmem, -, -, hRcard, -⟩ :=
    CFSG.Sporadic.SmallOddCore.mcl_normalizing_model
  have hPR : mclP ≤ mclR := fun p hp => (hRmem p).mpr (Or.inl hp)
  have hidx : (mclP.subgroupOf mclR).index = 2 := by
    have h := (mclP.subgroupOf mclR).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPR).toEquiv,
      CFSG.Sporadic.Schreier.card_mclP, hRcard] at h
    omega
  have hx2P : ((x * x : mclR) : Equiv.Perm (Fin 275)) ∈ mclP :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mul_self_mem_of_index_two hidx x)
  set w : mclP := ⟨_, hx2P⟩ with hwdef
  have hwc : ∀ c ∈ Subgroup.centralizer ({z} : Set mclP), w * c = c * w := by
    intro c hc
    apply Subtype.ext
    change (x : Equiv.Perm (Fin 275)) * x * c = c * (x * x)
    rw [mul_assoc, hxc c hc, ← mul_assoc, hxc c hc, mul_assoc]
  have hwC : w ∈ Subgroup.centralizer ({z} : Set mclP) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (hwc z (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
  have hwZ : (⟨w, hwC⟩ : Subgroup.centralizer ({z} : Set mclP)) ∈
      Subgroup.center (Subgroup.centralizer ({z} : Set mclP)) := by
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (hwc c c.2).symm
  obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem_center (centCharThree_mclP z hz) hwZ
  have hwk : w ^ 3 ^ k = 1 := congrArg Subtype.val hk
  have hwm : w ^ orderOf (e x) = 1 := by
    apply Subtype.ext
    change ((x * x : mclR) : Equiv.Perm (Fin 275)) ^ orderOf (e x) = 1
    rw [← Subgroup.coe_pow, ← sq, ← pow_mul, mul_comm, pow_mul, ← hox, pow_orderOf_eq_one,
      one_pow, Subgroup.coe_one]
  have hw1 : w = 1 := by
    have h1 : orderOf w ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hwk
    have h2 : orderOf w ∣ orderOf (e x) := orderOf_dvd_of_pow_eq_one hwm
    have hcop : Nat.Coprime (3 ^ k) (orderOf (e x)) := Nat.Coprime.pow_left k hσ.symm
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h1) h2)
  have hxx : x * x = 1 := by
    have h := congrArg Subtype.val hw1
    exact Subtype.ext h
  by_contra hσ1
  have hx1 : x ≠ 1 := fun h => hσ1 (by rw [h, map_one])
  have hxo : orderOf (x : Equiv.Perm (Fin 275)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq, hxx]) hx1
  obtain ⟨-, -, -, hrows, hcover, -, hlist, -⟩ :=
    CFSG.Sporadic.SmallOddCore.mcl_involution_centralizers
  obtain ⟨r, hr, g, hg, hxg⟩ := hcover x x.2 hxo
  obtain ⟨-, -, -, -, hcard, -⟩ := hrows r hr
  have hcard' : Nat.card (mclP ⊓ Subgroup.centralizer ({(x : Equiv.Perm (Fin 275))} :
      Set (Equiv.Perm (Fin 275))) : Subgroup (Equiv.Perm (Fin 275))) = r.centOrder := by
    rw [hxg, CFSG.Sporadic.SmallOddCore.inf_centralizer_conj mclP hg,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  have hco : r.centOrder = 40320 ∨ r.centOrder = 7920 := by
    have hmem : (r.outer, r.classSize, r.centOrder) ∈
        [(false, 22275, 40320), (true, 113400, 7920)] := by
      rw [← hlist]
      exact List.mem_map_of_mem hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨-, -, h⟩ | ⟨-, -, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have hle : (Subgroup.centralizer ({z} : Set mclP)).map mclP.subtype ≤
      mclP ⊓ Subgroup.centralizer ({(x : Equiv.Perm (Fin 275))} : Set (Equiv.Perm (Fin 275))) := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c.2, Subgroup.mem_centralizer_singleton_iff.mpr (hxc c hc).symm⟩
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective mclP.subtype_injective, hcard'] at hdvd
  rcases card_centralizer_mclP z hz with h | h <;> rcases hco with h' | h' <;>
    rw [h, h'] at hdvd <;> norm_num at hdvd

theorem alphaVanishes_mclP {D : Subgroup mclP} (hD : D ≠ ⊥) (hD3 : ∀ b ∈ D, b ^ 3 = 1) :
    AlphaVanishes mclP D := by
  have hord : ∀ b ∈ D, b ≠ 1 → orderOf b = 3 := fun b hb hb1 => orderOf_eq_prime (hD3 b hb) hb1
  refine alphaVanishes_of_rigid center_mclP_eq_bot hD (fun b hb hb1 => ?_)
    (fun b hb hb1 σ hσ hfix => eq_one_of_fix_mclP b (hord b hb hb1) σ hσ hfix)
  exact core_eq_bot_of_isCharacteristicP (centCharThree_mclP b (hord b hb hb1))

end McL

end Res423Three

open Res423Three

theorem k423SporMcL :
    K423SporMcL := by
  rintro X _ _ ⟨φ⟩
  have eM : NativeSporadic.Carrier .McL ≃* CFSG.Sporadic.Schreier.mclP :=
    CFSG.Sporadic.Schreier.mclPermEquiv
  set ψ : X ≃* CFSG.Sporadic.Schreier.mclP := φ.trans eM with hψ
  refine Res423Two.census423_of_alphaVanishes fun D hD hD9 =>
    Res423Two.alphaVanishes_of_mulEquiv ψ ?_
  refine alphaVanishes_mclP ?_ (Res423Two.isElemAbelian_map' _ hD.prop).2
  intro h
  have h9 : Nat.card (D.map ψ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ψ.injective, hD9]
  rw [h, Subgroup.card_bot] at h9
  omega

end CFSG.RankThree.PartTwo.Sec4
