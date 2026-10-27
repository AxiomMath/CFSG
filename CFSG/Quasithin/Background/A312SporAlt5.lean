module

public import CFSG.Quasithin.Background.A312SporGen

public section

namespace CFSG.Quasithin.A312S

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem eq_bot_of_perfect_of_solvable {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : ⁅H, H⁆ = H) (hs : Group.IsSolvable ↥H) : H = ⊥ := by
  have h1 := (isSolvable_iff_perfectCore_eq_bot H).mp hs
  rwa [perfectCore_eq_self_of_perfect hH] at h1

theorem eq_alt5_of_perfect {H : Subgroup (Equiv.Perm (Fin 5))} (hH : ⁅H, H⁆ = H) (hne : H ≠ ⊥) :
    H = alternatingGroup (Fin 5) := by
  have hHA : H ≤ alternatingGroup (Fin 5) := by
    rw [← hH]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [Equiv.Perm.mem_alternatingGroup, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hns : ¬ Group.IsSolvable ↥H := fun hs => hne (eq_bot_of_perfect_of_solvable hH hs)
  have hdvd : Nat.card H ∣ 60 := card_alt5 ▸ Subgroup.card_dvd_of_le hHA
  have hpos : 0 < Nat.card H := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hle : Nat.card H ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
  have h23 : ∀ a b : ℕ, Nat.card H = 2 ^ a * 3 ^ b → False := fun a b h =>
    hns (isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) h)
  have h25 : ∀ a b : ℕ, Nat.card H = 2 ^ a * 5 ^ b → False := fun a b h =>
    hns (isSolvable_of_card_pq Nat.prime_two (by norm_num) (by norm_num) h)
  have h35 : ∀ a b : ℕ, Nat.card H = 3 ^ a * 5 ^ b → False := fun a b h =>
    hns (isSolvable_of_card_pq Nat.prime_three (by norm_num) (by norm_num) h)
  have h30 : Nat.card H ≠ 30 := by
    intro h30
    have := Seven.alt5_simple
    have hc : Nat.card (H.subgroupOf (alternatingGroup (Fin 5))) = 30 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHA).toEquiv, h30]
    have hi : (H.subgroupOf (alternatingGroup (Fin 5))).index = 2 := by
      have h1 := Subgroup.card_mul_index (H.subgroupOf (alternatingGroup (Fin 5)))
      rw [hc, card_alt5] at h1
      omega
    have := Subgroup.normal_of_index_eq_two hi
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H.subgroupOf (alternatingGroup (Fin 5))) with
      h | h
    · rw [h, Subgroup.card_bot] at hc
      omega
    · rw [h, Subgroup.card_top, card_alt5] at hc
      omega
  have h60 : Nat.card H = 60 := by
    interval_cases hc : Nat.card H <;> first
      | omega
      | exact (h23 0 0 rfl).elim
      | exact (h23 1 0 rfl).elim
      | exact (h23 0 1 rfl).elim
      | exact (h23 2 0 rfl).elim
      | exact (h25 0 1 rfl).elim
      | exact (h23 1 1 rfl).elim
      | exact (h25 1 1 rfl).elim
      | exact (h23 2 1 rfl).elim
      | exact (h35 1 1 rfl).elim
      | exact (h25 2 1 rfl).elim
  exact Subgroup.eq_of_le_of_card_ge hHA (by rw [card_alt5, h60])

theorem card_eq_card_ker_mul_card_range {G H : Type} [Group G] [Group H] (φ : G →* H) :
    Nat.card G = Nat.card φ.ker * Nat.card φ.range := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, mul_comm]

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem exists_perm_five {Y Z : Subgroup Γ} (hidx : (Z.subgroupOf Y).index = 5) :
    ∃ φ : ↥Y →* Equiv.Perm (Fin 5), φ.ker ≤ Z.subgroupOf Y := by
  let e : (↥Y ⧸ Z.subgroupOf Y) ≃ Fin 5 := Finite.equivFinOfCardEq hidx
  refine ⟨(Equiv.permCongrHom e).toMonoidHom.comp
    (MulAction.toPermHom ↥Y (↥Y ⧸ Z.subgroupOf Y)), fun y hy => ?_⟩
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff] at hy
  have h1 : y • ((1 : ↥Y) : ↥Y ⧸ Z.subgroupOf Y) = ((1 : ↥Y) : ↥Y ⧸ Z.subgroupOf Y) := by
    have := congrArg (fun σ : Equiv.Perm (↥Y ⧸ Z.subgroupOf Y) =>
      σ ((1 : ↥Y) : ↥Y ⧸ Z.subgroupOf Y)) hy
    simpa using this
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq] at h1
  simpa using h1

theorem perfectCore_map_eq_alt5 {Y Z : Subgroup Γ} (φ : ↥Y →* Equiv.Perm (Fin 5))
    (hker : φ.ker ≤ Z.subgroupOf Y) (hZs : Group.IsSolvable ↥Z) (hYns : ¬ Group.IsSolvable ↥Y) :
    ((perfectCore Y).subgroupOf Y).map φ = alternatingGroup (Fin 5) := by
  have hPY : perfectCore Y ≤ Y := perfectCore_le Y
  have hPperf : ⁅perfectCore Y, perfectCore Y⁆ = perfectCore Y := perfectCore_perfect Y
  have hP'perf : ⁅(perfectCore Y).subgroupOf Y, (perfectCore Y).subgroupOf Y⁆ =
      (perfectCore Y).subgroupOf Y := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPY, hPperf]
  refine eq_alt5_of_perfect (by rw [← Subgroup.map_commutator, hP'perf]) fun hbot => hYns ?_
  have hPZ : perfectCore Y ≤ Z := by
    intro x hx
    have hx' : (⟨x, hPY hx⟩ : ↥Y) ∈ (perfectCore Y).subgroupOf Y := hx
    have h1 : φ ⟨x, hPY hx⟩ ∈ ((perfectCore Y).subgroupOf Y).map φ := ⟨_, hx', rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact hker h1
  have hPs : Group.IsSolvable ↥(perfectCore Y) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hPZ)
      (Subgroup.inclusion_injective hPZ)
  exact (isSolvable_iff_perfectCore_eq_bot Y).mpr (eq_bot_of_perfect_of_solvable hPperf hPs)

theorem lFamily_alt5_of_index_five {S B Y Z : Subgroup Γ} (hB : B ∈ lFamily S)
    (hY : B ⊔ S = Y) (hidx : (Z.subgroupOf Y).index = 5) (hZs : Group.IsSolvable ↥Z) {e : ℕ}
    (hcard : Nat.card ↥Y = 120 * 2 ^ e) (hO2 : Nat.card (CFSG.Open.pCoreOf 2 Y) ≤ 2 ^ e)
    (hquot : ∀ (N : Subgroup ↥Y) [N.Normal], IsPGroup 2 (↥Y ⧸ N) → Nat.card (↥Y ⧸ N) ≤ 2) :
    IsAlt 5 (ModO2 B) ∧ Nat.card (CFSG.pCore 2 ↥B) = 2 ^ e := by
  subst hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Seven.alt5_simple
  obtain ⟨φ, hker⟩ := exists_perm_five hidx
  have himg := perfectCore_map_eq_alt5 φ hker hZs (not_isSolvable_sup hB)
  have hPY : perfectCore (B ⊔ S) ≤ B ⊔ S := perfectCore_le _
  have hmem : ∀ x : ↥(perfectCore (B ⊔ S)),
      φ (Subgroup.inclusion hPY x) ∈ alternatingGroup (Fin 5) := fun x => by
    rw [← himg]
    exact ⟨Subgroup.inclusion hPY x, x.2, rfl⟩
  let f : ↥(perfectCore (B ⊔ S)) →* alternatingGroup (Fin 5) :=
    (φ.comp (Subgroup.inclusion hPY)).codRestrict _ hmem
  have hf : Function.Surjective f := by
    rintro ⟨σ, hσ⟩
    have hσ' : σ ∈ ((perfectCore (B ⊔ S)).subgroupOf (B ⊔ S)).map φ := by rw [himg]; exact hσ
    obtain ⟨y, hy, hyσ⟩ := hσ'
    exact ⟨⟨(y : Γ), hy⟩, Subtype.ext hyσ⟩
  let ι : ↥f.ker →* ↥φ.ker :=
    { toFun := fun x => ⟨Subgroup.inclusion hPY x.1, by
        have h := x.2
        rw [MonoidHom.mem_ker] at h ⊢
        exact congrArg Subtype.val h⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun x y h => by
    have := congrArg (fun z : ↥φ.ker => ((z : ↥(B ⊔ S)) : Γ)) h
    exact Subtype.ext (Subtype.ext this)
  let κ : ↥φ.ker →* ↥Z :=
    { toFun := fun x => ⟨((x : ↥(B ⊔ S)) : Γ), hker x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hκ : Function.Injective κ := fun x y h => by
    have := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext this)
  have hkerS : Group.IsSolvable ↥φ.ker := Group.isSolvable_of_isSolvable_injective hκ
  have hkerf : Group.IsSolvable ↥f.ker := Group.isSolvable_of_isSolvable_injective hι
  have hBP : B = perfectCore (B ⊔ S) := lFamily_eq_perfectCore hB Seven.alt5_nonabelian f hf hkerf
  have hA5le : alternatingGroup (Fin 5) ≤ φ.range := by
    rw [← himg]
    exact Subgroup.map_le_range φ _
  have h60 : 60 ∣ Nat.card φ.range := card_alt5 ▸ Subgroup.card_dvd_of_le hA5le
  have h120 : Nat.card φ.range ≤ 120 := by
    have h1 := Subgroup.card_subgroup_dvd_card φ.range
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 5), Fintype.card_fin,
      show Nat.factorial 5 = 120 from rfl] at h1
    exact Nat.le_of_dvd (by norm_num) h1
  have hrpos : 0 < Nat.card φ.range := Nat.card_pos
  have hYc := card_eq_card_ker_mul_card_range φ
  rw [hcard] at hYc
  have hkp : IsPGroup 2 ↥φ.ker := by
    obtain ⟨r, hr⟩ := h60
    refine IsPGroup.of_card_dvd_pow (n := e + 1) ⟨r, ?_⟩
    rw [hr] at hYc
    have h1 : 60 * (2 ^ (e + 1)) = 60 * (Nat.card φ.ker * r) := by
      calc 60 * (2 ^ (e + 1)) = 120 * 2 ^ e := by ring
        _ = Nat.card φ.ker * (60 * r) := hYc
        _ = 60 * (Nat.card φ.ker * r) := by ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h1
  have hkc : Nat.card φ.ker ≤ 2 ^ e := by
    have h1 := Subgroup.card_le_of_le
      (CFSG.LieType.BorelTits.le_pCore 2 (inferInstance : φ.ker.Normal) hkp)
    have h2 : Nat.card (CFSG.Open.pCore 2 ↥(B ⊔ S)) = Nat.card (CFSG.Open.pCoreOf 2 (B ⊔ S)) :=
      (Subgroup.card_map_of_injective (B ⊔ S).subtype_injective).symm
    omega
  have hkf2 : IsPGroup 2 ↥f.ker := hkp.of_injective ι hι
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card.mp hkf2)
  have hle : 2 ^ a ≤ 2 ^ e := ha ▸ (Nat.card_le_card_of_injective ι hι).trans hkc
  have hP : Nat.card ↥(perfectCore (B ⊔ S)) = 2 ^ a * 60 := by
    rw [card_eq_card_ker_mul_card_range f, ha, MonoidHom.range_eq_top.mpr hf,
      Subgroup.card_top, card_alt5]
  have hnorm := perfectCore_normal (B ⊔ S)
  have hQ := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((perfectCore (B ⊔ S)).subgroupOf (B ⊔ S))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPY).toEquiv, hP, hcard] at hQ
  have hQ' : Nat.card (↥(B ⊔ S) ⧸ (perfectCore (B ⊔ S)).subgroupOf (B ⊔ S)) * 2 ^ a =
      2 ^ (e + 1) := by
    have h1 : 60 * (Nat.card (↥(B ⊔ S) ⧸ (perfectCore (B ⊔ S)).subgroupOf (B ⊔ S)) * 2 ^ a) =
        60 * 2 ^ (e + 1) := by
      calc 60 * (Nat.card (↥(B ⊔ S) ⧸ (perfectCore (B ⊔ S)).subgroupOf (B ⊔ S)) * 2 ^ a)
          = Nat.card (↥(B ⊔ S) ⧸ (perfectCore (B ⊔ S)).subgroupOf (B ⊔ S)) * (2 ^ a * 60) := by
            ring
        _ = 120 * 2 ^ e := hQ.symm
        _ = 60 * 2 ^ (e + 1) := by ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h1
  have hQp : IsPGroup 2 (↥(B ⊔ S) ⧸ (perfectCore (B ⊔ S)).subgroupOf (B ⊔ S)) :=
    IsPGroup.of_card_dvd_pow (n := e + 1) ⟨2 ^ a, hQ'.symm⟩
  have hQ2 := hquot _ hQp
  have hQpos : 0 < Nat.card (↥(B ⊔ S) ⧸ (perfectCore (B ⊔ S)).subgroupOf (B ⊔ S)) :=
    Nat.card_pos
  have hae : 2 ^ a = 2 ^ e := by
    rw [pow_succ] at hQ'
    generalize Nat.card (↥(B ⊔ S) ⧸ (perfectCore (B ⊔ S)).subgroupOf (B ⊔ S)) = q at hQ' hQ2 hQpos
    generalize 2 ^ a = X at hQ' hle ⊢
    generalize 2 ^ e = Y at hQ' hle ⊢
    interval_cases q <;> omega
  rw [hBP]
  refine ⟨⟨modO2EquivOfHom Seven.alt5_nonabelian f hf hkf2⟩, ?_⟩
  rw [pCore_two_eq_ker Seven.alt5_nonabelian f hf hkf2, ha, hae]

end CFSG.Quasithin.A312S
