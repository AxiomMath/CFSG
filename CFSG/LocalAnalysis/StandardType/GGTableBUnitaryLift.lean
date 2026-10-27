module

public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover
public import Mathlib.GroupTheory.SchurZassenhaus

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

namespace TableBU

section TwoPart

variable {P : Type*} [Group P]

@[expose] def twoPartOf (C : Subgroup P) (hC : C ≤ Subgroup.center P) (M : ℕ) : Subgroup P where
  carrier := {c | c ∈ C ∧ c ^ 2 ^ M = 1}
  mul_mem' {a b} ha hb := by
    refine ⟨C.mul_mem ha.1 hb.1, ?_⟩
    have hab : Commute a b := (Subgroup.mem_center_iff.mp (hC ha.1) b).symm
    rw [hab.mul_pow, ha.2, hb.2, one_mul]
  one_mem' := ⟨C.one_mem, one_pow _⟩
  inv_mem' {a} ha := ⟨C.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem mem_twoPartOf {C : Subgroup P} {hC : C ≤ Subgroup.center P} {M : ℕ} {c : P} :
    c ∈ twoPartOf C hC M ↔ c ∈ C ∧ c ^ 2 ^ M = 1 :=
  Iff.rfl

theorem twoPartOf_le (C : Subgroup P) (hC : C ≤ Subgroup.center P) (M : ℕ) :
    twoPartOf C hC M ≤ C :=
  fun _ h => h.1

instance twoPartOf_normal (C : Subgroup P) (hC : C ≤ Subgroup.center P) (M : ℕ) :
    (twoPartOf C hC M).Normal :=
  ⟨fun n hn g => by
    have h1 : g * n = n * g := Subgroup.mem_center_iff.mp (hC hn.1) g
    rw [h1, mul_inv_cancel_right]
    exact hn⟩

theorem isPGroup_twoPartOf (C : Subgroup P) (hC : C ≤ Subgroup.center P) (M : ℕ) :
    IsPGroup 2 (twoPartOf C hC M) :=
  fun g => ⟨M, Subtype.ext (by simpa using g.2.2)⟩

theorem mem_twoPartOf_of_pow [Finite P] {C : Subgroup P} (hC : C ≤ Subgroup.center P) {c : P}
    (hc : c ∈ C) {k : ℕ} (hk : c ^ 2 ^ k = 1) : c ∈ twoPartOf C hC (Nat.card P) := by
  refine ⟨hc, ?_⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  have h1 : 2 ^ j ≤ Nat.card P := hj ▸ Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard c)
  have h2 : j ≤ Nat.card P := (Nat.lt_two_pow_self).le.trans h1
  rw [← orderOf_dvd_iff_pow_eq_one, hj]
  exact Nat.pow_dvd_pow 2 h2

end TwoPart

theorem coprime_two_card_of_sq {G : Type*} [Group G] [Finite G]
    (h : ∀ g : G, g ^ 2 = 1 → g = 1) : Nat.Coprime 2 (Nat.card G) := by
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro hd
  have := Fact.mk Nat.prime_two
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 hd
  have h1 := h g (by rw [← hg]; exact pow_orderOf_eq_one g)
  rw [h1, orderOf_one] at hg
  exact absurd hg (by norm_num)

section Lift

open CFSG.LieType.Steinberg

variable {H R L : Type} [Group H] [Group R] [Group L] [Finite H] [Finite L]

theorem sq_eq_one_ker_lift {ψ : L →* R} (hker : ψ.ker ≤ Subgroup.center L)
    (y : L ⧸ twoPartOf ψ.ker hker (Nat.card L))
    (hy : y ∈ (QuotientGroup.lift _ ψ (twoPartOf_le _ hker _)).ker) (hy2 : y ^ 2 = 1) :
    y = 1 := by
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (twoPartOf ψ.ker hker (Nat.card L)) y
  have hz : z ∈ ψ.ker := by
    rw [MonoidHom.mem_ker] at hy ⊢
    rwa [QuotientGroup.mk'_apply, QuotientGroup.lift_mk] at hy
  have hz2 : z ^ 2 ∈ twoPartOf ψ.ker hker (Nat.card L) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hy2
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine mem_twoPartOf_of_pow hker hz (k := Nat.card L + 1) ?_
  rw [pow_succ', pow_mul]
  exact hz2.2

theorem exists_lift_of_section (q : H →* R)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : H →* E, ∀ h, π (s h) = h)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E₀ U₀ : Subgroup H} (hE₀ : IsElemAbelian p E₀)
    (hE₀q : E₀ ⊓ q.ker = ⊥) (hU₀ : IsPGroup 2 U₀) (hU₀q : ¬ U₀ ≤ q.ker)
    (hEU : E₀ ≤ Subgroup.normalizer (U₀ : Set H)) (ψ : L →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) :
    ∃ U E : Subgroup L, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set L) ∧
      IsElemAbelian p E ∧ Nat.card E = Nat.card E₀ ∧ E ⊓ ψ.ker = ⊥ := by
  classical
  have := Fact.mk hp
  set N := twoPartOf ψ.ker hker (Nat.card L) with hNdef
  have hNk : N ≤ ψ.ker := twoPartOf_le _ hker _
  set π : L →* L ⧸ N := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hkerπ : π.ker = N := QuotientGroup.ker_mk' N
  set ψb : L ⧸ N →* R := QuotientGroup.lift N ψ hNk with hψb
  have hψbπ : ∀ l, ψb (π l) = ψ l := fun l => QuotientGroup.lift_mk N hNk l
  have hψbs : Function.Surjective ψb := by
    intro r
    obtain ⟨l, rfl⟩ := hψ r
    exact ⟨π l, hψbπ l⟩
  have hψbc : ψb.ker ≤ Subgroup.center (L ⧸ N) := by
    intro y hy
    obtain ⟨z, rfl⟩ := hπs y
    have hz : z ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, ← hψbπ]
      exact hy
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨v, rfl⟩ := hπs w
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hker hz) v]
  have hψbodd : ∀ y ∈ ψb.ker, y ^ 2 = 1 → y = 1 := fun y hy hy2 =>
    sq_eq_one_ker_lift hker y hy hy2
  set Pb := pullback q ψb with hPb
  have hfst := pullbackFst_surjective (β := q) hψbs
  have hfstc := ker_pullbackFst_le_center (β := q) hψbc
  have hcop : Nat.Coprime 2 (Nat.card (pullbackFst q ψb).ker) := by
    refine coprime_two_card_of_sq fun y hy2 => ?_
    obtain ⟨h1, h2⟩ := snd_mem_ker_of_mem_ker_pullbackFst y.2
    have h3 : (((y : Pb) : H × (L ⧸ N)).2) ^ 2 = 1 := by
      have := congrArg (fun z : (pullbackFst q ψb).ker => ((z : Pb) : H × (L ⧸ N)).2) hy2
      simpa using this
    have h4 := hψbodd _ h2 h3
    exact Subtype.ext (Subtype.ext (Prod.ext h1 h4))
  obtain ⟨σ, hσ⟩ := hsplit Pb (pullbackFst q ψb) hfst hfstc hcop
  set α : H →* L ⧸ N := ((MonoidHom.snd H (L ⧸ N)).comp Pb.subtype).comp σ with hαdef
  have hα : ∀ h, ψb (α h) = q h := by
    intro h
    have hmem := mem_pullback.1 (σ h).2
    have h1 : ((σ h : Pb) : H × (L ⧸ N)).1 = h := hσ h
    change ψb ((σ h : Pb) : H × (L ⧸ N)).2 = q h
    rw [← hmem, h1]
  set E' := E₀.map α with hE'
  have hinj : Function.Injective (α.comp E₀.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : q (a : H) = 1 := by
      rw [← hα, show α (a : H) = 1 from ha, map_one]
    have h2 : (a : H) ∈ E₀ ⊓ q.ker := ⟨a.2, h1⟩
    rw [hE₀q, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hE'card : Nat.card E' = Nat.card E₀ := by
    have h1 : (α.comp E₀.subtype).range = E' := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hE'ab : IsElemAbelian p E' := isElemAbelian_map hE₀ α
  set H' := E'.comap π with hH'
  have hNH' : N ≤ H' := by
    intro n hn
    have hn' : n ∈ π.ker := by
      rw [hkerπ]
      exact hn
    show π n ∈ E'
    rw [show π n = 1 from hn']
    exact E'.one_mem
  set f' : H' →* L ⧸ N := π.comp H'.subtype with hf'
  have hkerf' : f'.ker = N.subgroupOf H' := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show π h = 1 ↔ (h : L) ∈ N
    rw [← MonoidHom.mem_ker, hkerπ]
  have hrangef' : f'.range = E' := by
    ext y
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨h, rfl⟩
      exact h.2
    · intro hy
      obtain ⟨l, rfl⟩ := hπs y
      exact ⟨⟨l, hy⟩, rfl⟩
  have hindex : (N.subgroupOf H').index = Nat.card E₀ := by
    rw [← hkerf', Subgroup.index_ker, hrangef', hE'card]
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (isPGroup_twoPartOf ψ.ker hker (Nat.card L))
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hE₀)
  have hcardN' : Nat.card (N.subgroupOf H') = 2 ^ a := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH').toEquiv]
    exact ha
  have h2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr fun h => hp2 h.symm
  have hcop' : Nat.Coprime (Nat.card (N.subgroupOf H')) (N.subgroupOf H').index := by
    rw [hcardN', hindex, hm]
    exact Nat.Coprime.pow a m h2p
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime hcop'
  have hCcard : Nat.card C = Nat.card E₀ := by
    have h1 := hC.card_mul_card
    have h2 := Subgroup.card_mul_index (N.subgroupOf H')
    rw [← hindex]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
  set E : Subgroup L := C.map H'.subtype with hEdef
  have hEN : ∀ e ∈ E, π e = 1 → e = 1 := by
    rintro _ ⟨c, hc, rfl⟩ hce
    have hcN : c ∈ N.subgroupOf H' := by
      rw [← hkerf']
      exact hce
    have hc1 : c ∈ N.subgroupOf H' ⊓ C := ⟨hcN, hc⟩
    rw [hC.disjoint.eq_bot, Subgroup.mem_bot] at hc1
    rw [hc1]
    rfl
  have hEE' : ∀ e ∈ E, π e ∈ E' := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun e he => ?_⟩
    · have hc : (x : L) * y * (x : L)⁻¹ * (y : L)⁻¹ = 1 := by
        refine hEN _ (E.mul_mem (E.mul_mem (E.mul_mem x.2 y.2) (E.inv_mem x.2)) (E.inv_mem y.2)) ?_
        have hxy := IsElemAbelian.comm hE'ab (hEE' _ x.2) (hEE' _ y.2)
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxy]
        group
      show (x : L) * y = y * x
      calc (x : L) * y = (x : L) * y * (x : L)⁻¹ * (y : L)⁻¹ * (y * x) := by group
        _ = y * x := by rw [hc, one_mul]
    · refine hEN _ (E.pow_mem he p) ?_
      rw [map_pow]
      exact hE'ab.2 _ (hEE' e he)
  have hEcard : Nat.card E = Nat.card E₀ := by
    rw [hEdef, Subgroup.card_map_of_injective H'.subtype_injective, hCcard]
  have hEker : E ⊓ ψ.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro e ⟨heE, heK⟩
    obtain ⟨s, hs, hse⟩ := hEE' e heE
    have hqs : q s = 1 := by
      rw [← hα, hse, hψbπ]
      exact heK
    have hs1 : s ∈ E₀ ⊓ q.ker := ⟨hs, hqs⟩
    rw [hE₀q, Subgroup.mem_bot] at hs1
    rw [hs1, map_one] at hse
    exact (Subgroup.mem_bot).mpr (hEN e heE hse.symm)
  set U : Subgroup L := (U₀.map α).comap π with hUdef
  have hU2 : IsPGroup 2 U := by
    refine (hU₀.map α).comap_of_ker_isPGroup π ?_
    rw [hkerπ]
    exact isPGroup_twoPartOf _ _ _
  have hUne : U ≠ ⊥ := by
    obtain ⟨u, huU, huq⟩ := Set.not_subset.mp hU₀q
    obtain ⟨l, hl⟩ := hπs (α u)
    have hlU : l ∈ U := ⟨u, huU, hl.symm⟩
    have hl1 : l ≠ 1 := by
      rintro rfl
      apply huq
      show q u = 1
      rw [← hα, ← hl, map_one, map_one]
    intro h
    rw [h, Subgroup.mem_bot] at hlU
    exact hl1 hlU
  have hEU' : E ≤ Subgroup.normalizer (U : Set L) := by
    intro e he
    obtain ⟨s, hs, hse⟩ := hEE' e he
    have hαs : α s ∈ Subgroup.normalizer ((U₀.map α : Subgroup (L ⧸ N)) : Set (L ⧸ N)) :=
      Subgroup.le_normalizer_map α ⟨s, hEU hs, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro l
    rw [hUdef, Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv, ← hse]
    exact Subgroup.mem_normalizer_iff.mp hαs (π l)
  exact ⟨U, E, hUne, hU2, hEU', hEab, hEcard, hEker⟩

end Lift

end TableBU

end CFSG.StandardType
