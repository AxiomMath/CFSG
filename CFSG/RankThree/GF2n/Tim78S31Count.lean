module

public import CFSG.RankThree.GF2n.Tim78S31Aut

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G]

namespace NCPair

variable {U V : Subgroup G} (P : NCPair U V) (hCen : BenderCenterInput)
  (hU : UnitaryTwoGenerationInput)
include P hCen hU

theorem card_N : Nat.card ↥(PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) =
    Nat.card ↥(PartTwo.omegaOneSub U) * Nat.card ↥(PartTwo.omegaOneSub V) := by
  have hUV : U ⊓ V = ⊥ := P.setup.inf_eq_bot P.ne
  let f : ↥(PartTwo.omegaOneSub U) × ↥(PartTwo.omegaOneSub V) →
      ↥(PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) := fun p =>
    ⟨(p.1 : G) * p.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2)
      (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨u, v⟩ ⟨u', v'⟩ h
      have h' : (u : G) * v = u' * v' := congrArg Subtype.val h
      have hw : (u' : G)⁻¹ * u ∈ U ⊓ V := by
        refine Subgroup.mem_inf.mpr ⟨U.mul_mem (U.inv_mem (PartTwo.omegaOneSub_le _ u'.2))
          (PartTwo.omegaOneSub_le _ u.2), ?_⟩
        rw [show (u' : G)⁻¹ * u = v' * (v : G)⁻¹ by
          calc (u' : G)⁻¹ * u = (u' : G)⁻¹ * (u * v) * (v : G)⁻¹ := by group
            _ = (u' : G)⁻¹ * (u' * v') * (v : G)⁻¹ := by rw [h']
            _ = v' * (v : G)⁻¹ := by group]
        exact V.mul_mem (PartTwo.omegaOneSub_le _ v'.2) (V.inv_mem (PartTwo.omegaOneSub_le _ v.2))
      rw [hUV, Subgroup.mem_bot, inv_mul_eq_one] at hw
      have hv : (v : G) = v' := by
        calc (v : G) = (u : G)⁻¹ * (u * v) := by group
          _ = (u : G)⁻¹ * (u' * v') := by rw [h']
          _ = v' := by rw [← hw]; group
      exact Prod.ext (Subtype.ext hw.symm) (Subtype.ext hv)
    · rintro ⟨n, hn⟩
      obtain ⟨u, hu, v, hv, rfl⟩ := P.exists_mul hCen hU hn
      exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem relIndex_le_card :
    (PartTwo.omegaOneSub U).relIndex U ≤ Nat.card ↥(PartTwo.omegaOneSub U) := by
  have hUV : U ⊓ V = ⊥ := P.setup.inf_eq_bot P.ne
  have hV₀ : PartTwo.omegaOneSub V ≠ ⊥ := by
    rw [← P.nrm_eq' hCen hU]
    exact P.setup.symm.ne_bot
  obtain ⟨⟨v, hv⟩, hv1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV₀
  have hv1 : v ≠ 1 := fun h => hv1' (Subtype.ext h)
  have hvN : v ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V := Subgroup.mem_sup_right hv
  have hvU : v ∉ PartTwo.omegaOneSub U := fun h => hv1 (by
    have : v ∈ U ⊓ V :=
      Subgroup.mem_inf.mpr ⟨PartTwo.omegaOneSub_le _ h, PartTwo.omegaOneSub_le _ hv⟩
    rwa [hUV, Subgroup.mem_bot] at this)
  have hk : ∀ u ∈ U, u * v * u⁻¹ * v⁻¹ ∈ PartTwo.omegaOneSub U := fun u hu =>
    P.comm_mem hCen hU hu hvN
  let f : ↥U →* ↥(PartTwo.omegaOneSub U) :=
    { toFun := fun u => ⟨(u : G) * v * (u : G)⁻¹ * v⁻¹, hk u u.2⟩
      map_one' := Subtype.ext (by
        show ((1 : ↥U) : G) * v * ((1 : ↥U) : G)⁻¹ * v⁻¹ = 1
        simp)
      map_mul' := fun a b => Subtype.ext (by
        show ((a * b : ↥U) : G) * v * ((a * b : ↥U) : G)⁻¹ * v⁻¹ =
          ((a : G) * v * (a : G)⁻¹ * v⁻¹) * ((b : G) * v * (b : G)⁻¹ * v⁻¹)
        have hka := hk a a.2
        have hkb := hk b b.2
        have h1 : (a : G) * ((b : G) * v * (b : G)⁻¹ * v⁻¹) =
            ((b : G) * v * (b : G)⁻¹ * v⁻¹) * a :=
          P.setup.comm _ a.2 _ (PartTwo.omegaOneSub_le _ hkb)
        have h2 : ((a : G) * v * (a : G)⁻¹ * v⁻¹) * ((b : G) * v * (b : G)⁻¹ * v⁻¹) =
            ((b : G) * v * (b : G)⁻¹ * v⁻¹) * ((a : G) * v * (a : G)⁻¹ * v⁻¹) :=
          P.setup.comm _ (PartTwo.omegaOneSub_le _ hka) _ (PartTwo.omegaOneSub_le _ hkb)
        rw [Subgroup.coe_mul, h2]
        calc (a : G) * b * v * ((a : G) * b)⁻¹ * v⁻¹ =
            (a : G) * ((b : G) * v * (b : G)⁻¹ * v⁻¹) * v * (a : G)⁻¹ * v⁻¹ := by group
          _ = ((b : G) * v * (b : G)⁻¹ * v⁻¹) * a * v * (a : G)⁻¹ * v⁻¹ := by rw [h1]
          _ = ((b : G) * v * (b : G)⁻¹ * v⁻¹) * ((a : G) * v * (a : G)⁻¹ * v⁻¹) := by
              group) }
  have hker : f.ker = (PartTwo.omegaOneSub U).subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : (u : G) * v * (u : G)⁻¹ * v⁻¹ = 1 := congrArg Subtype.val h
      have hc : (u : G) * v = v * u := by
        calc (u : G) * v = ((u : G) * v * (u : G)⁻¹ * v⁻¹) * (v * u) := by group
          _ = v * u := by rw [h', one_mul]
      by_contra hu
      exact hvU (P.cent hCen hU u.2 hu hvN hc)
    · intro hu
      apply Subtype.ext
      show (u : G) * v * (u : G)⁻¹ * v⁻¹ = 1
      rw [P.comm_N hCen hU (Subgroup.mem_sup_left hu) hvN]
      group
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  exact Nat.card_le_card_of_injective (fun z : Set.range f => (z : ↥(PartTwo.omegaOneSub U)))
    Subtype.val_injective

end NCPair

namespace Data31

variable {U : Subgroup G} {g α x : G} (D : Data31 U g α x) (hCen : BenderCenterInput)
  (hU : UnitaryTwoGenerationInput)
include D hCen hU

theorem pairAC : NCPair (conjSubgroup g U) (conjSubgroup x U) := by
  have K := D.core
  have hαA : α ∈ conjSubgroup g U := PartTwo.omegaOneSub_le _ D.mem
  exact ⟨{ comm := K.comm_conj' g
           two := K.two_conj g
           exp_ne := K.exp_ne_conj g
           ti := isTI_conjSubgroup K.ti g
           conj := ⟨x * g⁻¹, by rw [← conjSubgroup_mul, inv_mul_cancel_right]⟩
           ne_bot := fun hbot => D.ne_one (by
             have : α ∈ conjSubgroup g U ⊓ Subgroup.normalizer (conjSubgroup x U : Set G) :=
               Subgroup.mem_inf.mpr ⟨hαA, conjSubgroup_eq_self_iff.mp D.fix⟩
             rwa [hbot, Subgroup.mem_bot] at this) },
    K.exp_conj g, fun h => D.not_comm_CA hCen hU fun c hc a ha => (h a ha c hc).symm⟩

theorem comm_mem_C₀' {a c : G} (ha : a ∈ PartTwo.omegaOneSub (conjSubgroup g U))
    (hc : c ∈ conjSubgroup x U) :
    a * c * a⁻¹ * c⁻¹ ∈ PartTwo.omegaOneSub (conjSubgroup x U) := by
  have h := (D.pairAC hCen hU).symm.comm_mem hCen hU hc (Subgroup.mem_sup_right ha)
  have := (PartTwo.omegaOneSub (conjSubgroup x U)).inv_mem h
  rwa [show (c * a * c⁻¹ * a⁻¹)⁻¹ = a * c * a⁻¹ * c⁻¹ by group] at this

theorem exists_c {a : G} (ha : a ∈ PartTwo.omegaOneSub (conjSubgroup g U)) (ha1 : a ≠ 1) :
    ∃ c ∈ conjSubgroup x U,
      (∀ n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup a U),
        a * n * a⁻¹ = c * n * c⁻¹) ∧
      (∀ z ∈ U ⊔ conjSubgroup a U, (c * z * c⁻¹)⁻¹ * (a * z * a⁻¹) ∈
        PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup a U)) ∧
      conjSubgroup a U = conjSubgroup c U := by
  have K := D.core
  have Pa := D.pair_a hCen hU ha ha1
  have haa : a * a = 1 := K.sq_omega ha
  obtain ⟨xa, hxa, hCa, hfixa⟩ := D.fix_a hCen hU ha ha1
  have hfixa' : conjSubgroup a (conjSubgroup xa U) = conjSubgroup xa U := by
    rw [hCa]
    exact hfixa
  have hyC : ∀ c ∈ conjSubgroup xa U,
      a * c * a⁻¹ * c⁻¹ ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup a U) := by
    intro c hc
    rw [hCa] at hc
    have h := D.comm_mem_C₀' hCen hU ha hc
    rw [← hCa] at h
    exact Pa.omega_conj_le_N hCen hU hxa h
  obtain ⟨c, hc, hcz⟩ := Pa.exists_inner hCen hU haa rfl hxa hyC
  have hcX : c ∈ U ⊔ conjSubgroup a U := by
    rw [show c = xa * (xa⁻¹ * c * xa) * xa⁻¹ by group]
    exact (U ⊔ conjSubgroup a U).mul_mem ((U ⊔ conjSubgroup a U).mul_mem hxa
      (Subgroup.mem_sup_left (mem_conjSubgroup.mp hc))) ((U ⊔ conjSubgroup a U).inv_mem hxa)
  have hy : ∀ z ∈ U ⊔ conjSubgroup a U, c⁻¹ * a * z * (c⁻¹ * a)⁻¹ * z⁻¹ ∈
      PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup a U) := by
    intro z hz
    have h1 := Pa.conj_mem_N hCen hU ((U ⊔ conjSubgroup a U).mul_mem hz
      ((U ⊔ conjSubgroup a U).inv_mem hcX)) (hcz z hz)
    rwa [show z * c⁻¹ * ((c * z * c⁻¹)⁻¹ * (a * z * a⁻¹)) * (z * c⁻¹)⁻¹ =
      c⁻¹ * a * z * (c⁻¹ * a)⁻¹ * z⁻¹ by group] at h1
  have hyN : ∀ n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup a U),
      c⁻¹ * a * n * (c⁻¹ * a)⁻¹ * n⁻¹ ∈ PartTwo.omegaOneSub (conjSubgroup xa U) := by
    intro n hn
    have hk := Pa.commutator_mem_omega_of_swap hCen hU haa ha1 rfl ha hxa hfixa' hn
    have hk' := Pa.comm_mem_conj hCen hU hxa ((conjSubgroup xa U).inv_mem hc) hn
    have hcomm : c⁻¹ * (a * n * a⁻¹ * n⁻¹) * c = a * n * a⁻¹ * n⁻¹ := by
      have h1 := Tim78.comm_conj K.comm xa _ ((conjSubgroup xa U).inv_mem hc) _
        (PartTwo.omegaOneSub_le _ hk)
      calc c⁻¹ * (a * n * a⁻¹ * n⁻¹) * c = (a * n * a⁻¹ * n⁻¹) * c⁻¹ * c := by rw [h1]
        _ = a * n * a⁻¹ * n⁻¹ := by group
    have e : c⁻¹ * a * n * (c⁻¹ * a)⁻¹ * n⁻¹ =
        (c⁻¹ * (a * n * a⁻¹ * n⁻¹) * c) * (c⁻¹ * n * c⁻¹⁻¹ * n⁻¹) := by group
    rw [e, hcomm]
    exact Subgroup.mul_mem _ hk hk'
  have hne : conjSubgroup xa U ≠ U := by
    rw [hCa]
    exact fun h => D.ne_C h.symm
  have hcent : ∀ n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup a U),
      c⁻¹ * a * n * (c⁻¹ * a)⁻¹ = n := fun n hn =>
    Pa.commute_of_trivial_mod hCen hU hxa hne hy hyN hn
  have hU' := Pa.conj_eq_of_trivial_mod hCen hU (U ⊔ conjSubgroup a U).one_mem hy hcent
  rw [conjSubgroup_one] at hU'
  refine ⟨c, by rw [← hCa]; exact hc, fun n hn => ?_, hcz, ?_⟩
  · have h1 := hcent n hn
    calc a * n * a⁻¹ = c * (c⁻¹ * a * n * (c⁻¹ * a)⁻¹) * c⁻¹ := by group
      _ = c * n * c⁻¹ := by rw [h1]
  · calc conjSubgroup a U = conjSubgroup (c * (c⁻¹ * a)) U := by rw [mul_inv_cancel_left]
      _ = conjSubgroup c (conjSubgroup (c⁻¹ * a) U) := conjSubgroup_mul _ _ _
      _ = conjSubgroup c U := by rw [hU']

theorem sup_eq {a : G} (ha : a ∈ PartTwo.omegaOneSub (conjSubgroup g U)) (ha1 : a ≠ 1) :
    U ⊔ conjSubgroup a U = U ⊔ conjSubgroup x U := by
  obtain ⟨c, hc, -, -, he⟩ := D.exists_c hCen hU ha ha1
  obtain ⟨xa, hxa, hCa, -⟩ := D.fix_a hCen hU ha ha1
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [he]
    intro z hz
    rw [mem_conjSubgroup] at hz
    rw [show z = c * (c⁻¹ * z * c) * c⁻¹ by group]
    exact (U ⊔ conjSubgroup x U).mul_mem ((U ⊔ conjSubgroup x U).mul_mem
      (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hz))
      ((U ⊔ conjSubgroup x U).inv_mem (Subgroup.mem_sup_right hc))
  · refine sup_le le_sup_left ?_
    rw [← hCa]
    intro z hz
    rw [mem_conjSubgroup] at hz
    rw [show z = xa * (xa⁻¹ * z * xa) * xa⁻¹ by group]
    exact (U ⊔ conjSubgroup a U).mul_mem ((U ⊔ conjSubgroup a U).mul_mem hxa
      (Subgroup.mem_sup_left hz)) ((U ⊔ conjSubgroup a U).inv_mem hxa)

theorem N_eq {a : G} (ha : a ∈ PartTwo.omegaOneSub (conjSubgroup g U)) (ha1 : a ≠ 1) :
    PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup a U) =
      PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U) := by
  obtain ⟨c, hc, -, -, he⟩ := D.exists_c hCen hU ha ha1
  obtain ⟨xa, hxa, hCa, -⟩ := D.fix_a hCen hU ha ha1
  have Pa := D.pair_a hCen hU ha ha1
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [he, omegaOneSub_conj D.core.comm]
    intro z hz
    rw [mem_conjSubgroup] at hz
    have h1 := Pa.comm_mem_conj hCen hU hxa (by rw [hCa]; exact hc)
      (Subgroup.mem_sup_left hz)
    rw [hCa] at h1
    rw [show z = (c * (c⁻¹ * z * c) * c⁻¹ * (c⁻¹ * z * c)⁻¹) * (c⁻¹ * z * c) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hz)
  · refine sup_le le_sup_left ?_
    rw [← hCa]
    exact Pa.omega_conj_le_N hCen hU hxa

theorem act {a : G} (ha : a ∈ PartTwo.omegaOneSub (conjSubgroup g U)) :
    ∃ c ∈ conjSubgroup x U,
      (∀ n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U),
        a * n * a⁻¹ = c * n * c⁻¹) ∧
      ∀ z ∈ U ⊔ conjSubgroup x U, (c * z * c⁻¹)⁻¹ * (a * z * a⁻¹) ∈
        PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U) := by
  by_cases ha1 : a = 1
  · refine ⟨1, (conjSubgroup x U).one_mem, fun n _ => by rw [ha1], fun z _ => ?_⟩
    rw [ha1, inv_mul_cancel]
    exact Subgroup.one_mem _
  · obtain ⟨c, hc, hn, hz, -⟩ := D.exists_c hCen hU ha ha1
    rw [D.N_eq hCen hU ha ha1] at hn hz
    rw [D.sup_eq hCen hU ha ha1] at hz
    exact ⟨c, hc, hn, hz⟩

theorem eq_of_act {a a' c c' : G} (ha : a ∈ PartTwo.omegaOneSub (conjSubgroup g U))
    (ha' : a' ∈ PartTwo.omegaOneSub (conjSubgroup g U))
    (hn : ∀ n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U),
      a * n * a⁻¹ = c * n * c⁻¹)
    (hn' : ∀ n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U),
      a' * n * a'⁻¹ = c' * n * c'⁻¹)
    (hcc : c⁻¹ * c' ∈ PartTwo.omegaOneSub (conjSubgroup x U)) : a = a' := by
  have K := D.core
  have P := D.pair
  have hN := D.N_eq hCen hU D.mem D.ne_one
  obtain ⟨β, hβ, hβ1⟩ := K.exists_ne_one_omega 1
  rw [conjSubgroup_one] at hβ
  have hβN : β ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U) :=
    Subgroup.mem_sup_left hβ
  have hk : c⁻¹ * c' * β = β * (c⁻¹ * c') := by
    have h1 : c⁻¹ * c' ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup α U) := by
      rw [hN]
      exact Subgroup.mem_sup_right hcc
    exact P.comm_N hCen hU h1 (Subgroup.mem_sup_left hβ)
  have e1 : a * β * a⁻¹ = a' * β * a'⁻¹ := by
    rw [hn β hβN, hn' β hβN]
    calc c * β * c⁻¹ = c * (c⁻¹ * c' * β) * (c⁻¹ * c')⁻¹ * c⁻¹ := by rw [hk]; group
      _ = c' * β * c'⁻¹ := by group
  have hc : (a'⁻¹ * a) * β = β * (a'⁻¹ * a) := by
    calc (a'⁻¹ * a) * β = a'⁻¹ * (a * β * a⁻¹) * a := by group
      _ = a'⁻¹ * (a' * β * a'⁻¹) * a := by rw [e1]
      _ = β * (a'⁻¹ * a) := by group
  have hmem : a'⁻¹ * a ∈ PartTwo.omegaOneSub (conjSubgroup g U) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ ha') ha
  by_contra hne
  have hne' : a'⁻¹ * a ≠ 1 := fun h' => hne (by rw [inv_mul_eq_one] at h'; exact h'.symm)
  exact K.not_comm hmem hne' hβ hβ1 hc

omit [Finite G] hCen hU in
theorem relIndex_C : (PartTwo.omegaOneSub (conjSubgroup x U)).relIndex (conjSubgroup x U) =
    (PartTwo.omegaOneSub U).relIndex U := by
  rw [omegaOneSub_conj D.core.comm x, conjSubgroup, conjSubgroup,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj x).injective]

theorem exists_injective : ∃ F : ↥(PartTwo.omegaOneSub (conjSubgroup g U)) → ↥(conjSubgroup x U),
    Function.Injective (fun a => (QuotientGroup.mk (F a) : ↥(conjSubgroup x U) ⧸
      (PartTwo.omegaOneSub (conjSubgroup x U)).subgroupOf (conjSubgroup x U))) ∧
    ∀ a : ↥(PartTwo.omegaOneSub (conjSubgroup g U)),
      (∀ n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U),
        (a : G) * n * (a : G)⁻¹ = F a * n * (F a : G)⁻¹) ∧
      ∀ z ∈ U ⊔ conjSubgroup x U, ((F a : G) * z * (F a : G)⁻¹)⁻¹ * ((a : G) * z * (a : G)⁻¹) ∈
        PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U) := by
  have hex : ∀ a : ↥(PartTwo.omegaOneSub (conjSubgroup g U)), ∃ c : ↥(conjSubgroup x U),
      (∀ n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U),
        (a : G) * n * (a : G)⁻¹ = c * n * (c : G)⁻¹) ∧
      ∀ z ∈ U ⊔ conjSubgroup x U, ((c : G) * z * (c : G)⁻¹)⁻¹ * ((a : G) * z * (a : G)⁻¹) ∈
        PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U) := by
    intro a
    obtain ⟨c, hc, hn, hz⟩ := D.act hCen hU a.2
    exact ⟨⟨c, hc⟩, hn, hz⟩
  choose F hF using hex
  refine ⟨F, fun a a' h => ?_, hF⟩
  have h1 := QuotientGroup.eq.mp h
  rw [Subgroup.mem_subgroupOf] at h1
  exact Subtype.ext (D.eq_of_act hCen hU a.2 a'.2 (hF a).1 (hF a').1 (by simpa using h1))

theorem card_le : Nat.card ↥(PartTwo.omegaOneSub U) ≤ (PartTwo.omegaOneSub U).relIndex U := by
  obtain ⟨F, hinj, -⟩ := D.exists_injective hCen hU
  have hcard := Nat.card_le_card_of_injective _ hinj
  rwa [← Subgroup.index, ← Subgroup.relIndex, D.core.card_omega_conj g, D.relIndex_C] at hcard

theorem card_eq : Nat.card ↥(PartTwo.omegaOneSub U) = (PartTwo.omegaOneSub U).relIndex U :=
  le_antisymm (D.card_le hCen hU) (D.pair.relIndex_le_card hCen hU)

theorem exists_a {c : G} (hc : c ∈ conjSubgroup x U) :
    ∃ a ∈ PartTwo.omegaOneSub (conjSubgroup g U), ∃ c' ∈ conjSubgroup x U,
      c⁻¹ * c' ∈ PartTwo.omegaOneSub (conjSubgroup x U) ∧
      (∀ n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U),
        a * n * a⁻¹ = c' * n * c'⁻¹) ∧
      ∀ z ∈ U ⊔ conjSubgroup x U, (c' * z * c'⁻¹)⁻¹ * (a * z * a⁻¹) ∈
        PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup x U) := by
  obtain ⟨F, hinj, hF⟩ := D.exists_injective hCen hU
  have hbij := hinj.bijective_of_nat_card_le (by
    rw [← Subgroup.index, ← Subgroup.relIndex, D.relIndex_C, ← D.card_eq hCen hU,
      D.core.card_omega_conj g])
  obtain ⟨a, ha⟩ := hbij.2 (QuotientGroup.mk ⟨c, hc⟩)
  have h1 := QuotientGroup.eq.mp ha
  rw [Subgroup.mem_subgroupOf] at h1
  refine ⟨a, a.2, F a, (F a).2, ?_, (hF a).1, (hF a).2⟩
  have := (PartTwo.omegaOneSub (conjSubgroup x U)).inv_mem h1
  simpa using this

end Data31

end CFSG.RankThree.GF2n.Tim78
