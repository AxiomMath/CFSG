module

public import CFSG.Quasithin.Recognition.RuTypeJ210c

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem card_normalizer_eq_mul [Finite G] (Y : Subgroup G) :
    Nat.card (Subgroup.normalizer (Y : Set G)) =
      Nat.card (Subgroup.centralizer (Y : Set G)) * Nat.card (autNHom Y).range := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (autNHom Y).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (autNHom Y)).toEquiv] at h1
  rw [h1, mul_comm]
  congr 1
  refine Nat.card_congr
    { toFun := fun g => ⟨((g : Subgroup.normalizer (Y : Set G)) : G), ?_⟩
      invFun := fun c => ⟨⟨c, Subgroup.centralizer_le_normalizer _ c.2⟩, ?_⟩
      left_inv := fun g => rfl
      right_inv := fun c => rfl }
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (mem_ker_autNHom.mp g.2 y hy).symm
  · rw [mem_ker_autNHom]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp c.2 y hy).symm

namespace RuDataM

variable (M : RuDataM G) [Finite G]

omit [Finite G] in
theorem comm_Y {p : ℕ} (hp : p = 7 ∨ p = 13) {Y : Subgroup G} (hY : Nat.card Y = p) {y y' : G}
    (hy : y ∈ Y) (hy' : y' ∈ Y) : y * y' = y' * y := by
  have : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> norm_num⟩
  have hcyc : IsCyclic Y := isCyclic_of_prime_card hY
  exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨y, hy⟩ : Y) ⟨y', hy'⟩)

theorem conj_mem_S0_of_normalizes
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {p : ℕ}
    (hp : p = 7 ∨ p = 13) {Y : Subgroup G} (hYL : Y ≤ Ls s) (hY : Nat.card Y = p) {g : G}
    (hg : g ∈ Subgroup.normalizer (Y : Set G)) {a : G} (ha : a ∈ M.S0) :
    g * a * g⁻¹ ∈ M.S0 := by
  have hcY : ∀ y ∈ Y, (g * a * g⁻¹) * y = y * (g * a * g⁻¹) := by
    intro y hy
    have hy' : g⁻¹ * y * g ∈ Y := by
      refine (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * y * g)).mpr ?_
      have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rw [e]
      exact hy
    have h1 := M.comm_S0_Ls hs hs1 ha (hYL hy')
    calc g * a * g⁻¹ * y = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * a) * g⁻¹ := by rw [h1]
      _ = y * (g * a * g⁻¹) := by group
  obtain ⟨a', ha', y', hy', he⟩ := M.exists_S0_mul_of_centralizes hs hs1 hp hYL hY hcY
  have h2 : (a' * y') ^ 2 ^ 1 = 1 := by
    rw [← he, pow_one, pow_two]
    have haa : a * a = 1 := by rw [← pow_two]; exact M.S0_elem.2 a ha
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [haa]; group
  have hy1 := M.eq_one_of_two_elt hp hY ha' hy' (M.comm_S0_Ls hs hs1 ha' (hYL hy')) h2
  rw [he, hy1, mul_one]
  exact ha'

theorem mem_Cen_of_normalizes_pow
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {p : ℕ}
    (hp : p = 7 ∨ p = 13) {Y : Subgroup G} (hYL : Y ≤ Ls s) (hY : Nat.card Y = p) {g : G}
    (hg : g ∈ Subgroup.normalizer (Y : Set G)) {k : ℕ} (hk : g ^ p ^ k = 1) : g ∈ Cen s := by
  have hgS : g ∈ Subgroup.normalizer (M.S0 : Set G) :=
    mem_normalizer_of_conj_mem fun a ha => M.conj_mem_S0_of_normalizes hs hs1 hp hYL hY hg ha
  have h1 : orderOf (autNHom M.S0 ⟨g, hgS⟩) ∣ p ^ k := by
    refine (orderOf_map_dvd _ _).trans (orderOf_dvd_of_pow_eq_one ?_)
    exact Subtype.ext (by simpa using hk)
  have hinj : Function.Injective (MulAut.toPerm M.S0) := fun a b h =>
    MulEquiv.ext fun x => congrArg (fun f : Equiv.Perm M.S0 => f x) h
  have h2 : orderOf (autNHom M.S0 ⟨g, hgS⟩) ∣ Nat.factorial 4 := by
    rw [← orderOf_injective _ hinj, ← M.card_S0, ← Nat.card_perm]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (p ^ k) (Nat.factorial 4) :=
    Nat.Coprime.pow_left _ (by rcases hp with rfl | rfl <;> decide)
  have h3 : orderOf (autNHom M.S0 ⟨g, hgS⟩) = 1 := by
    have h4 : orderOf (autNHom M.S0 ⟨g, hgS⟩) ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd h1 h2
    exact Nat.dvd_one.mp h4
  have hker : (⟨g, hgS⟩ : Subgroup.normalizer (M.S0 : Set G)) ∈ (autNHom M.S0).ker := by
    rw [MonoidHom.mem_ker]
    exact orderOf_eq_one_iff.mp h3
  rw [mem_Cen]
  exact mem_ker_autNHom.mp hker s hs

theorem card_of_sylow_Ls
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {p : ℕ} (hp : p = 7 ∨ p = 13)
    {Y : Subgroup G} (hYL : Y ≤ Ls s)
    (hYQ : ∃ Q : Sylow p (Ls s), (Q : Subgroup (Ls s)) = Y.subgroupOf (Ls s)) :
    Nat.card Y = p := by
  obtain ⟨Q, hQ⟩ := hYQ
  have : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> norm_num⟩
  rw [← card_subgroupOf_of_le hYL, ← hQ, Q.card_eq_multiplicity, M.card_Ls hs hs1]
  rcases hp with rfl | rfl
  · rw [factorization_29120_seven, pow_one]
  · rw [factorization_29120_thirteen, pow_one]

theorem exists_sylow_Y
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {p : ℕ} (hp : p = 7 ∨ p = 13)
    {Y : Subgroup G} (hYL : Y ≤ Ls s) (hY : Nat.card Y = p) :
    ∃ Q : Sylow p G, (Q : Subgroup G) = Y := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hpp⟩
  have hYp : IsPGroup p Y := by
    rw [IsPGroup.iff_card, hY]
    exact ⟨1, (pow_one p).symm⟩
  refine ⟨{ toSubgroup := Y, isPGroup' := hYp, is_maximal' := fun {Q} hQ hle => ?_ }, rfl⟩
  by_contra hne
  set S := Y.subgroupOf Q with hSdef
  have hlt : S < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne (le_antisymm (fun x hx => ?_) hle)
    have : (⟨x, hx⟩ : Q) ∈ S := by rw [h]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  have : Group.IsNilpotent Q := hQ.isNilpotent
  obtain ⟨q, hqN, hqS⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent S hlt)
  have hqY : (q : G) ∈ Subgroup.normalizer (Y : Set G) := by
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    have hyS : (⟨y, hle hy⟩ : Q) ∈ S := Subgroup.mem_subgroupOf.mpr hy
    have h := (Subgroup.mem_normalizer_iff.mp hqN _).mp hyS
    rw [hSdef, Subgroup.mem_subgroupOf] at h
    simpa using h
  obtain ⟨k, hk⟩ := hQ q
  have hk' : (q : G) ^ p ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hqC := M.mem_Cen_of_normalizes_pow hs hs1 hp hYL hY hqY hk'
  have hodd : Odd (orderOf (q : G)) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hpp).mp (orderOf_dvd_of_pow_eq_one hk')
    rw [hi]
    exact Odd.pow (by rcases hp with rfl | rfl <;> decide)
  obtain ⟨-, -, h3⟩ := M.sylowLs_props hs hs1 hp hYL hY
  have hq := h3 _ (mem_Ls_of_odd hqC hodd)
    (fun y hy => (Subgroup.mem_normalizer_iff.mp hqY y).mp hy) k hk'
  exact hqS (Subgroup.mem_subgroupOf.mpr hq)

theorem card_centralizer_Y
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {p : ℕ} (hp : p = 7 ∨ p = 13)
    {Y : Subgroup G} (hYL : Y ≤ Ls s) (hY : Nat.card Y = p) :
    Nat.card (Subgroup.centralizer (Y : Set G)) = 4 * p := by
  have hS0X := M.S0_le_centralizer hs hs1 hYL
  have hYX : Y ≤ Subgroup.centralizer (Y : Set G) := fun y hy => by
    rw [Subgroup.mem_centralizer_iff]
    intro y' hy'
    exact comm_Y hp hY hy' hy
  let f : M.S0 × Y → Subgroup.centralizer (Y : Set G) := fun x =>
    ⟨(x.1 : G) * x.2, mul_mem (hS0X x.1.2) (hYX x.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨y, hy⟩⟩ ⟨⟨a', ha'⟩, ⟨y', hy'⟩⟩ h
      have h' : a * y = a' * y' := congrArg Subtype.val h
      have hm : a'⁻¹ * a = y' * y⁻¹ := by
        calc a'⁻¹ * a = a'⁻¹ * (a * y) * y⁻¹ := by group
          _ = a'⁻¹ * (a' * y') * y⁻¹ := by rw [h']
          _ = y' * y⁻¹ := by group
      have hS : a'⁻¹ * a ∈ M.S0 := mul_mem (inv_mem ha') ha
      have hYm : a'⁻¹ * a ∈ Y := by
        rw [hm]
        exact mul_mem hy' (inv_mem hy)
      have h1 : a'⁻¹ * a = 1 := M.eq_one_of_two_elt hp hY (one_mem _) hYm
        (by rw [one_mul, mul_one]) (k := 1) (by rw [one_mul, pow_one]; exact M.S0_elem.2 _ hS)
      have haa : a = a' := by
        calc a = a' * (a'⁻¹ * a) := by group
          _ = a' := by rw [h1, mul_one]
      subst haa
      have hyy : y = y' := mul_left_cancel h'
      subst hyy
      rfl
    · rintro ⟨x, hx⟩
      obtain ⟨a, ha, y, hy, rfl⟩ := M.exists_S0_mul_of_centralizes hs hs1 hp hYL hY
        (fun y hy => (Subgroup.mem_centralizer_iff.mp hx y hy).symm)
      exact ⟨(⟨a, ha⟩, ⟨y, hy⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, M.card_S0, hY]

theorem card_autG_Y
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {p : ℕ} (hp : p = 7 ∨ p = 13)
    {Y : Subgroup G} (hYL : Y ≤ Ls s) (hY : Nat.card Y = p) :
    Nat.card (autNHom Y).range = p - 1 := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hpp⟩
  have hcyc : IsCyclic Y := isCyclic_of_prime_card hY
  have hAut : Nat.card (MulAut Y) = p - 1 := by
    rw [IsCyclic.card_mulAut, hY, Nat.totient_prime hpp]
  have hR : Nat.card (autNHom Y).range ∣ p - 1 := hAut ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨l, -, hlY, hlc⟩ := M.exists_conj_three hs hs1 hp hYL hY
  have hgN : l * M.bel * l⁻¹ ∈ Subgroup.normalizer (Y : Set G) := mem_normalizer_of_conj_mem hlY
  have h3 : orderOf (autNHom Y ⟨l * M.bel * l⁻¹, hgN⟩) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ ?_
    · have hg3 : (⟨l * M.bel * l⁻¹, hgN⟩ : Subgroup.normalizer (Y : Set G)) ^ 3 = 1 := by
        apply Subtype.ext
        rw [SubgroupClass.coe_pow]
        show (l * M.bel * l⁻¹) ^ 3 = 1
        rw [conj_pow, M.bel_pow_three]
        group
      rw [← map_pow, hg3, map_one]
    · intro h1
      exact hlc (mem_ker_autNHom.mp (MonoidHom.mem_ker.mpr h1))
  have h3R : 3 ∣ Nat.card (autNHom Y).range :=
    h3 ▸ Subgroup.orderOf_dvd_natCard _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  obtain ⟨hC, -, -⟩ := M.sylowLs_props hs hs1 hp hYL hY
  let P : Sylow p (Ls s) := Sylow.ofCard (Y.subgroupOf (Ls s)) (M.card_sylowLs hs hs1 hp hYL hY)
  have hPc : (P : Subgroup (Ls s)) = Y.subgroupOf (Ls s) := rfl
  have hNcard : Nat.card (Subgroup.normalizer ((P : Subgroup (Ls s)) : Set (Ls s))) =
      p * ((p - 1) / 3) := by
    rcases hp with rfl | rfl
    · exact (M.normalizer_Ls_seven hs hs1 P).1
    · exact (M.normalizer_Ls_thirteen hs hs1 P).1
  have hNY : ∀ x : Subgroup.normalizer ((P : Subgroup (Ls s)) : Set (Ls s)),
      ((x : Ls s) : G) ∈ Subgroup.normalizer (Y : Set G) := fun x =>
    mem_normalizer_of_conj_mem fun y hy => by
      have hyP : (⟨y, hYL hy⟩ : Ls s) ∈ (P : Subgroup (Ls s)) := Subgroup.mem_subgroupOf.mpr hy
      have h : (x : Ls s) * ⟨y, hYL hy⟩ * (x : Ls s)⁻¹ ∈ Y.subgroupOf (Ls s) :=
        (Subgroup.mem_normalizer_iff.mp x.2 _).mp hyP
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h
  let f : Subgroup.normalizer ((P : Subgroup (Ls s)) : Set (Ls s)) →*
      Subgroup.normalizer (Y : Set G) :=
    { toFun := fun x => ⟨((x : Ls s) : G), hNY x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hker : ((autNHom Y).comp f).ker = (P : Subgroup (Ls s)).subgroupOf
      (Subgroup.normalizer ((P : Subgroup (Ls s)) : Set (Ls s))) := by
    ext x
    change f x ∈ (autNHom Y).ker ↔ ((x : Ls s) : G) ∈ Y
    constructor
    · intro h
      exact hC _ (x : Ls s).2 (mem_ker_autNHom.mp h)
    · intro h
      rw [mem_ker_autNHom]
      intro y hy
      exact comm_Y hp hY h hy
  have hcardK : Nat.card ((autNHom Y).comp f).ker = p := by
    rw [hker, card_subgroupOf_of_le Subgroup.le_normalizer, hPc, card_subgroupOf_of_le hYL, hY]
  have hrange : Nat.card ((autNHom Y).comp f).range = (p - 1) / 3 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((autNHom Y).comp f).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ((autNHom Y).comp f)).toEquiv,
      hNcard, hcardK, mul_comm] at h1
    exact (Nat.eq_of_mul_eq_mul_right hpp.pos h1).symm
  have hle : ((autNHom Y).comp f).range ≤ (autNHom Y).range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, rfl⟩
  have hmR : (p - 1) / 3 ∣ Nat.card (autNHom Y).range := hrange ▸ Subgroup.card_dvd_of_le hle
  have hcop : Nat.Coprime 3 ((p - 1) / 3) := by rcases hp with rfl | rfl <;> decide
  have h := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h3R hmR
  have he : 3 * ((p - 1) / 3) = p - 1 := by rcases hp with rfl | rfl <;> rfl
  rw [he] at h
  exact Nat.dvd_antisymm hR h

omit [Finite G] in
theorem isCyclic_autG_Y {p : ℕ} (hp : p = 7 ∨ p = 13) {Y : Subgroup G} (hY : Nat.card Y = p) :
    IsCyclic (autNHom Y).range := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hpp⟩
  have hcyc : IsCyclic Y := isCyclic_of_prime_card hY
  have hU : IsCyclic (ZMod (Nat.card Y))ˣ := by
    rw [hY]
    exact ZMod.isCyclic_units_prime hpp
  have : IsCyclic (MulAut Y) :=
    isCyclic_of_surjective (IsCyclic.mulAutMulEquiv Y).symm.toMonoidHom
      (IsCyclic.mulAutMulEquiv Y).symm.surjective
  infer_instance

theorem card_normalizer_Y
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {p : ℕ} (hp : p = 7 ∨ p = 13)
    {Y : Subgroup G} (hYL : Y ≤ Ls s) (hY : Nat.card Y = p) :
    Nat.card (Subgroup.normalizer (Y : Set G)) = 4 * p * (p - 1) := by
  rw [card_normalizer_eq_mul, M.card_centralizer_Y hs hs1 hp hYL hY,
    M.card_autG_Y hs hs1 hp hYL hY]

theorem lemma_J210
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {p : ℕ} (hp : p = 7 ∨ p = 13)
    {Y : Subgroup G} (hYL : Y ≤ Ls s)
    (hYQ : ∃ Q : Sylow p (Ls s), (Q : Subgroup (Ls s)) = Y.subgroupOf (Ls s)) :
    ((∃ P : Sylow p G, (P : Subgroup G) = Y) ∧ Nat.card Y = p) ∧
    Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (M.S0 : Set G) ∧
    (Y ⊔ M.S0 = Subgroup.centralizer (Y : Set G) ∧
      IsCyclic (autNHom Y).range ∧ Nat.card (autNHom Y).range = p - 1) := by
  have hY := M.card_of_sylow_Ls hs hs1 hp hYL hYQ
  refine ⟨⟨M.exists_sylow_Y hs hs1 hp hYL hY, hY⟩, fun g hg =>
    mem_normalizer_of_conj_mem fun a ha => M.conj_mem_S0_of_normalizes hs hs1 hp hYL hY hg ha,
    le_antisymm ?_ ?_, isCyclic_autG_Y hp hY, M.card_autG_Y hs hs1 hp hYL hY⟩
  · refine sup_le (fun y hy => ?_) (M.S0_le_centralizer hs hs1 hYL)
    rw [Subgroup.mem_centralizer_iff]
    intro y' hy'
    exact comm_Y hp hY hy' hy
  · intro x hx
    obtain ⟨a, ha, y, hy, rfl⟩ := M.exists_S0_mul_of_centralizes hs hs1 hp hYL hY
      (fun y hy => (Subgroup.mem_centralizer_iff.mp hx y hy).symm)
    exact mul_mem (Subgroup.mem_sup_right ha) (Subgroup.mem_sup_left hy)

end RuDataM

end CFSG.Quasithin.RuType
