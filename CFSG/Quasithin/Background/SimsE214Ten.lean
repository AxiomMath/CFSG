module

public import CFSG.Quasithin.Background.SimsE2DihSemi
public import CFSG.Quasithin.Background.SimsE2Dih
public import CFSG.Quasithin.Background.SimsE214Eleven
public import CFSG.Sporadic.Schreier.J4SNoCompCover
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace Dih

theorem r_pow {n : ℕ} (k : ZMod n) (m : ℕ) :
    DihedralGroup.r k ^ m = DihedralGroup.r ((m : ZMod n) * k) := by
  induction m with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, DihedralGroup.r_zero]
  | succ m ih => rw [pow_succ, ih, DihedralGroup.r_mul_r, Nat.cast_succ, add_mul, one_mul]

theorem exists_eq_sr {n : ℕ} (hn : Odd n) {x : DihedralGroup n} (hx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ i, x = DihedralGroup.sr i := by
  rcases x with i | i
  · exfalso
    apply hx1
    rw [DihedralGroup.r_mul_r, DihedralGroup.one_def, DihedralGroup.r.injEq] at hx
    rw [E2.eq_zero_of_add_self_eq_zero hn hx, DihedralGroup.r_zero]
  · exact ⟨i, rfl⟩

theorem sr_mul_sr_pow {n : ℕ} (i j : ZMod n) :
    (DihedralGroup.sr i * DihedralGroup.sr j) ^ n = 1 := by
  rw [DihedralGroup.sr_mul_sr, r_pow, ZMod.natCast_self, zero_mul, DihedralGroup.r_zero]

theorem two_ne_zero_zmod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_ofNat]; exact h
  rw [CharP.cast_eq_zero_iff (ZMod p) p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')

theorem r_one_mem_of_normal {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {K : Subgroup (DihedralGroup p)} (hK : K.Normal) {z : DihedralGroup p} (hz : z ∈ K)
    (hz1 : z ≠ 1) : DihedralGroup.r 1 ∈ K := by
  have hrot : ∀ i : ZMod p, i ≠ 0 → DihedralGroup.r i ∈ K → DihedralGroup.r 1 ∈ K := by
    intro i hi hri
    have e : DihedralGroup.r i ^ (i⁻¹ : ZMod p).val = DihedralGroup.r 1 := by
      rw [r_pow, ZMod.natCast_zmod_val, inv_mul_cancel₀ hi]
    rw [← e]
    exact K.pow_mem hri _
  rcases z with i | i
  · exact hrot i (fun h => hz1 (by rw [h, DihedralGroup.r_zero])) hz
  · have h1 : DihedralGroup.sr (i - 2) ∈ K := by
      have := hK.conj_mem _ hz (DihedralGroup.r 1)
      rw [DihedralGroup.r_mul_sr, DihedralGroup.inv_r, DihedralGroup.sr_mul_r] at this
      convert this using 2
      ring
    have h2 := K.mul_mem hz h1
    rw [DihedralGroup.sr_mul_sr] at h2
    refine hrot _ ?_ h2
    rw [sub_sub_cancel_left]
    exact neg_ne_zero.2 (two_ne_zero_zmod (Fact.out) hp2)

theorem inv_apply_mem {N : Type*} [Group N] [Finite N] {σ : MulAut N} {U : Subgroup N}
    (hσ : ∀ u ∈ U, σ u ∈ U) : ∀ u ∈ U, σ⁻¹ u ∈ U := by
  have hle : U.map σ.toMonoidHom ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    exact hσ u hu
  have heq : U.map σ.toMonoidHom = U :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective σ.injective])
  intro u hu
  rw [← heq] at hu
  obtain ⟨u', hu', rfl⟩ := hu
  rw [MulEquiv.coe_toMonoidHom, MulAut.inv_apply_self]
  exact hu'

section Lift

variable {Γ : Type*} [Group Γ] {P Z : Subgroup Γ} [(Z.subgroupOf P).Normal]

@[expose] def liftSec (U : Subgroup (↥P ⧸ Z.subgroupOf P)) : Subgroup Γ :=
  (U.comap (QuotientGroup.mk' (Z.subgroupOf P))).map P.subtype

theorem mem_liftSec {U : Subgroup (↥P ⧸ Z.subgroupOf P)} {y : Γ} :
    y ∈ liftSec U ↔ ∃ hy : y ∈ P, ((⟨y, hy⟩ : P) : ↥P ⧸ Z.subgroupOf P) ∈ U := by
  constructor
  · rintro ⟨⟨y, hy⟩, hyU, rfl⟩
    exact ⟨hy, hyU⟩
  · rintro ⟨hy, hyU⟩
    exact ⟨⟨y, hy⟩, hyU, rfl⟩

theorem liftSec_le (U : Subgroup (↥P ⧸ Z.subgroupOf P)) : liftSec U ≤ P := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem le_liftSec (hZP : Z ≤ P) (U : Subgroup (↥P ⧸ Z.subgroupOf P)) : Z ≤ liftSec U :=
  fun z hz => mem_liftSec.2 ⟨hZP hz, by
    rw [(QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hz)]
    exact U.one_mem⟩

theorem liftSec_mono {U U' : Subgroup (↥P ⧸ Z.subgroupOf P)} (h : U ≤ U') :
    liftSec U ≤ liftSec U' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem liftSec_bot_le : liftSec (⊥ : Subgroup (↥P ⧸ Z.subgroupOf P)) ≤ Z := by
  intro y hy
  obtain ⟨hyP, hy1⟩ := mem_liftSec.1 hy
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hy1
  exact hy1

theorem liftSec_inf_le (U U' : Subgroup (↥P ⧸ Z.subgroupOf P)) :
    liftSec U ⊓ liftSec U' ≤ liftSec (U ⊓ U') := by
  rintro y ⟨h1, h2⟩
  obtain ⟨hy, hyU⟩ := mem_liftSec.1 h1
  obtain ⟨hy', hyU'⟩ := mem_liftSec.1 h2
  exact mem_liftSec.2 ⟨hy, hyU, hyU'⟩

theorem relIndex_liftSec (hZP : Z ≤ P) (U : Subgroup (↥P ⧸ Z.subgroupOf P)) :
    Z.relIndex (liftSec U) = Nat.card U := by
  set f := QuotientGroup.mk' (Z.subgroupOf P) with hf
  have hZ : (Z.subgroupOf P).map P.subtype = Z := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hZP]
  have hker : f.ker = Z.subgroupOf P := QuotientGroup.ker_mk' _
  have key : (f.domRestrict (U.comap f)).ker = (Z.subgroupOf P).subgroupOf (U.comap f) := by
    rw [MonoidHom.ker_domRestrict, hker]
  calc Z.relIndex (liftSec U) = ((Z.subgroupOf P).map P.subtype).relIndex (liftSec U) := by
        rw [hZ]
    _ = (Z.subgroupOf P).relIndex (U.comap f) :=
        Subgroup.relIndex_map_map_of_injective _ _ P.subtype_injective
    _ = Nat.card U := by
        rw [Subgroup.relIndex, ← key, Subgroup.index_ker, MonoidHom.domRestrict_range,
          Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

theorem iSup_liftSec {ι : Type*} [Nonempty ι] (U : ι → Subgroup (↥P ⧸ Z.subgroupOf P))
    (hU : ⨆ i, U i = ⊤) : ⨆ i, liftSec (U i) = P := by
  set f := QuotientGroup.mk' (Z.subgroupOf P) with hf
  have hX : ⨆ i, (U i).comap f = ⊤ := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    have hker : f.ker ≤ ⨆ i, (U i).comap f :=
      (Subgroup.ker_le_comap f (U i₀)).trans (le_iSup (fun i => (U i).comap f) i₀)
    have hsurj : Function.Surjective f := QuotientGroup.mk'_surjective _
    rw [← Subgroup.comap_map_eq_self hker, Subgroup.map_iSup]
    simp_rw [Subgroup.map_comap_eq_self_of_surjective hsurj]
    rw [hU, Subgroup.comap_top]
  change ⨆ i, ((U i).comap f).map P.subtype = P
  rw [← Subgroup.map_iSup, hX, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end Lift

end Dih

open Dih

theorem e214_ten {Γ : Type} [Group Γ] [Finite Γ] (H T M V : Subgroup Γ)
    (h : E2.Hyp28 H T M V) : CharTwo H → IsTISetIn V M →
    ∀ (I : Subgroup Γ) (g : Γ), IsInIHTV H T M V I → g ∈ I → I = V ⊔ conjSubgroup V g →
      V ⊓ conjSubgroup V g ≠ ⊥ →
      ∀ (MI TI JI B A P Z : Subgroup Γ) (k : ℕ),
        MI = M ⊓ I → TI = T ⊓ I → JI = kerIn MI I → B = V ⊓ pCoreOf 2 I →
        A = conjSubgroup V g ⊓ pCoreOf 2 I → P = A ⊔ B → Z = V ⊓ conjSubgroup V g →
        E1.nParam (⊤ : Subgroup (E2.StarQuot MI I)) = (k : ℕ∞) →
        ∀ p : ℕ, p.Prime → p ≠ 2 → Nonempty (E2.StarQuot MI I ≃* DihedralGroup p) →
          ∃ (r : ℕ) (W : Fin r → Subgroup Γ),
            (∀ i, Z ≤ W i ∧ W i ≤ P ∧ IsFaithfulIrredSection I (W i) Z JI ∧
              E3.mQuot (W i) Z = 2 * E2.dParamPrime p) ∧
            (⨆ i, W i) = P ∧ ∀ i, W i ⊓ (⨆ j, ⨆ (_ : j ≠ i), W j) ≤ Z := by
  intro hc _ I g hI hg hgen _ MI TI JI B A P Z k hMI _ hJI hB hA hP hZ _ p hp hp2 ⟨e⟩
  subst hMI hJI hB hA hP hZ
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have econj := E214E.conjSubgroup_eq_conjSub_inv V g
  have hpr := E214E.pair_of_isInIHTV h hI hg hgen
  have hgen' : I = V ⊔ B6.conjSub g⁻¹ V := by rw [← econj]; exact hgen
  have hcharI : CharTwo I := by
    have := E2.charTwo_of_charTwo h (hI.1 (I.inv_mem hg)) hc
    rwa [← hgen'] at this
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hidx := hpr.relIndex_eq_two_of_dihedral hodd e
  obtain ⟨hPO, hOJ, -⟩ := hpr.e2_10_six hidx
  set B' := kerIn (M ⊓ I) I ⊓ V with hB'
  set A' := B6.conjSub g⁻¹ B' with hA'
  set P' := B' ⊔ A' with hP'
  set Z' := V ⊓ B6.conjSub g⁻¹ V with hZ'
  have hPeq : conjSubgroup V g ⊓ pCoreOf 2 I ⊔ V ⊓ pCoreOf 2 I = P' := by
    rw [econj, ← hpr.conjSub_kerIn_inf_eq, ← hpr.kerIn_inf_eq, sup_comm]
  have hZeq : V ⊓ conjSubgroup V g = Z' := by rw [econj]
  rw [hPeq, hZeq]
  have hPI : P' ≤ I := hpr.P_le_X
  have hZP : Z' ≤ P' := hpr.inf_conj_le_P
  have hIP : I ≤ Subgroup.normalizer (P' : Set Γ) := hpr.le_normalizer_P
  have hIZ : I ≤ Subgroup.normalizer (Z' : Set Γ) := hpr.le_normalizer_Z
  have hPO' : P' = pCoreOf 2 I := hPO
  have hJP : ∀ x : Γ, x ∈ kerIn (M ⊓ I) I → x ∈ P' := fun x hx => by
    rw [hPO', hOJ]
    exact hx
  have hPJ : ∀ x : Γ, x ∈ P' → x ∈ kerIn (M ⊓ I) I := fun x hx => by
    rw [← hOJ, ← hPO']
    exact hx
  haveI : (Z'.subgroupOf P').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZP).2 (hPI.trans hIZ)
  set ρ := conjSecAut P' Z' I hIP hIZ with hρ
  have hcomm : ∀ x y : ↥P' ⧸ Z'.subgroupOf P', x * y = y * x := by
    intro x y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e1 : (((x * y)⁻¹ * (y * x) : P') : Γ) =
        (y : Γ)⁻¹ * (x : Γ)⁻¹ * (y : Γ)⁻¹⁻¹ * (x : Γ)⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e1]
    exact (hpr.commutator_sq_mem_Z (P'.inv_mem y.2) (P'.inv_mem x.2)).1
  have hsq : ∀ x : ↥P' ⧸ Z'.subgroupOf P', x * x = 1 := by
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_mul, ← pow_two]
    exact (hpr.commutator_sq_mem_Z x.2 x.2).2
  have hfix : ∀ (x : I) (y : Γ) (hy : y ∈ P'),
      ρ x ((⟨y, hy⟩ : P') : ↥P' ⧸ Z'.subgroupOf P') = ((⟨y, hy⟩ : P') : ↥P' ⧸ Z'.subgroupOf P') ↔
        (x : Γ) * y * (x : Γ)⁻¹ * y⁻¹ ∈ Z' := by
    intro x y hy
    rw [hρ, conjSecAut_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hyI : y ∈ I := hPI hy
    have e1 : (x : Γ) * y * (x : Γ)⁻¹ * y⁻¹ =
        y * (((x : Γ) * y * (x : Γ)⁻¹)⁻¹ * y)⁻¹ * y⁻¹ := by group
    have hN := Subgroup.mem_normalizer_iff.mp (hIZ hyI)
    change ((x : Γ) * y * (x : Γ)⁻¹)⁻¹ * y ∈ Z' ↔ _
    rw [e1]
    constructor
    · intro hz
      exact (hN _).mp (Z'.inv_mem hz)
    · intro hz
      have := Z'.inv_mem ((hN _).mpr hz)
      rwa [inv_inv] at this
  set q := QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) with hq
  have hker : ∀ x : I, q x = 1 → ρ x = 1 := by
    intro x hx
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
    rw [hρ, conjSecAut_eq_one_iff]
    intro y hy
    exact (hpr.commutator_sq_mem_Z (hJP _ hx) hy).1
  have hρq : ∀ x y : I, q x = q y → ρ x = ρ y := by
    intro x y hxy
    have h1 : q (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have h2 := hker _ h1
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  have hqP : ∀ (x : I), (x : Γ) ∈ P' → q x = 1 := by
    intro x hx
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hPJ _ hx
  obtain ⟨v, hvV, hvB⟩ : ∃ v ∈ V, v ∉ B' := by
    by_contra hne
    push Not at hne
    have h1 : B'.relIndex V = 1 := Subgroup.relIndex_eq_one.2 hne
    rw [hidx] at h1
    exact absurd h1 (by norm_num)
  have hvI : v ∈ I := hpr.V_le hvV
  have hv2 : v * v = 1 := by rw [← pow_two]; exact h.elem.2 v hvV
  set w := g⁻¹ * v * g with hw
  have hwV : w ∈ B6.conjSub g⁻¹ V := by
    rw [B6.mem_conjSub, inv_inv, hw]
    convert hvV using 1
    group
  have hwI : w ∈ I := hpr.conj_le hwV
  have hw2 : w * w = 1 := by
    rw [hw]
    calc g⁻¹ * v * g * (g⁻¹ * v * g) = g⁻¹ * (v * v) * g := by group
      _ = 1 := by rw [hv2]; group
  set t : I := ⟨v, hvI⟩ with ht
  set c : I := ⟨v * w, I.mul_mem hvI hwI⟩ with hcdef
  set τ := ρ t with hτdef
  set γ := ρ c with hγdef
  have hτ : τ * τ = 1 := by
    rw [hτdef, ← map_mul]
    convert map_one ρ using 2
    exact Subtype.ext hv2
  have hτγ : τ * γ * τ⁻¹ = γ⁻¹ := by
    rw [hτdef, hγdef, ← map_mul, ← map_inv, ← map_mul, ← map_inv]
    congr 1
    apply Subtype.ext
    simp only [ht, hcdef, Subgroup.coe_mul, Subgroup.coe_inv]
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
    rw [mul_inv_rev, hvi, hwi, ← mul_assoc, hv2, one_mul]
  have hρw : ρ ⟨w, hwI⟩ = τ * γ := by
    have e1 : (⟨w, hwI⟩ : I) = t * c := Subtype.ext (by
      show w = v * (v * w)
      rw [← mul_assoc, hv2, one_mul])
    rw [e1, map_mul]
  have hidx' : (B'.subgroupOf V).index = 2 := hidx
  have hdich : ∀ u ∈ V, u ∈ B' ∨ v⁻¹ * u ∈ B' := by
    intro u hu
    by_cases huB : u ∈ B'
    · exact Or.inl huB
    · right
      have key := Subgroup.mul_mem_iff_of_index_two hidx' (a := ⟨v⁻¹, V.inv_mem hvV⟩)
        (b := ⟨u, hu⟩)
      simp only [Subgroup.mem_subgroupOf] at key
      have hv' : v⁻¹ ∉ B' := fun h' => hvB (by simpa using B'.inv_mem h')
      exact key.2 (iff_of_false hv' huB)
  have hρV : ∀ u (hu : u ∈ V), ρ ⟨u, hpr.V_le hu⟩ = 1 ∨ ρ ⟨u, hpr.V_le hu⟩ = τ := by
    intro u hu
    rcases hdich u hu with hb | hb
    · exact Or.inl (hker _ (hqP _ (Subgroup.mem_sup_left hb)))
    · right
      have e1 : (⟨u, hpr.V_le hu⟩ : I) = t * ⟨v⁻¹ * u, I.mul_mem (I.inv_mem hvI) (hpr.V_le hu)⟩ :=
        Subtype.ext (by show u = v * (v⁻¹ * u); group)
      have h1 : ρ ⟨v⁻¹ * u, I.mul_mem (I.inv_mem hvI) (hpr.V_le hu)⟩ = 1 :=
        hker _ (hqP _ (Subgroup.mem_sup_left hb))
      rw [e1, map_mul, h1, mul_one]
  have hρVg : ∀ z (hz : z ∈ B6.conjSub g⁻¹ V),
      ρ ⟨z, hpr.conj_le hz⟩ = 1 ∨ ρ ⟨z, hpr.conj_le hz⟩ = τ * γ := by
    intro z hz
    have hz' : g * z * g⁻¹ ∈ V := by
      have := (B6.mem_conjSub).1 hz
      rwa [inv_inv] at this
    rcases hdich _ hz' with hb | hb
    · left
      refine hker _ (hqP _ (Subgroup.mem_sup_right ?_))
      rw [hA', B6.mem_conjSub, inv_inv]
      exact hb
    · right
      have hb' : w⁻¹ * z ∈ A' := by
        rw [hA', B6.mem_conjSub, inv_inv]
        convert hb using 1
        rw [hw]
        group
      have e1 : (⟨z, hpr.conj_le hz⟩ : I) =
          ⟨w, hwI⟩ * ⟨w⁻¹ * z, I.mul_mem (I.inv_mem hwI) (hpr.conj_le hz)⟩ :=
        Subtype.ext (by show z = w * (w⁻¹ * z); group)
      have h1 : ρ ⟨w⁻¹ * z, I.mul_mem (I.inv_mem hwI) (hpr.conj_le hz)⟩ = 1 :=
        hker _ (hqP _ (Subgroup.mem_sup_right hb'))
      rw [e1, map_mul, h1, mul_one, hρw]
  have hboth : ∀ a : ↥P' ⧸ Z'.subgroupOf P', τ a = a → (τ * γ) a = a → a = 1 := by
    intro a h1 h2
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective a
    have hyB : y ∈ B' := by
      refine hpr.mem_B_of_commutator_mem_Z hy fun u hu => ?_
      refine (hfix ⟨u, hpr.V_le hu⟩ y hy).1 ?_
      rcases hρV u hu with h | h <;> rw [h]
      · rfl
      · exact h1
    have hyA : y ∈ A' := by
      have hgI : g ∈ I := hg
      have hy' : g * y * g⁻¹ ∈ P' := (Subgroup.mem_normalizer_iff.mp (hIP hgI) y).mp hy
      have hB : g * y * g⁻¹ ∈ B' := by
        refine hpr.mem_B_of_commutator_mem_Z hy' fun u hu => ?_
        have hzV : g⁻¹ * u * g ∈ B6.conjSub g⁻¹ V := by
          rw [B6.mem_conjSub, inv_inv]
          convert hu using 1
          group
        have h3 : g⁻¹ * u * g * y * (g⁻¹ * u * g)⁻¹ * y⁻¹ ∈ Z' := by
          refine (hfix ⟨_, hpr.conj_le hzV⟩ y hy).1 ?_
          rcases hρVg _ hzV with h | h <;> rw [h]
          · rfl
          · exact h2
        have h4 := (Subgroup.mem_normalizer_iff.mp (hIZ hgI) _).mp h3
        convert h4 using 1
        group
      rw [hA', B6.mem_conjSub, inv_inv]
      exact hB
    have hBA : B' ⊓ A' = Z' := hpr.B_inf_A
    have hyZ : y ∈ Z' := by
      rw [← hBA]
      exact ⟨hyB, hyA⟩
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hyZ)
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hfree : fixSub γ = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    replace ha : γ a = a := ha
    have hγi : γ⁻¹ a = a := by
      conv_lhs => rw [← ha]
      rw [MulAut.inv_apply_self]
    have hτγτ : ∀ b, τ (γ (τ b)) = γ⁻¹ b := by
      intro b
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← hτγ, hτinv]
    have hττ : ∀ x, τ (τ x) = x := fun x => by rw [← MulAut.mul_apply, hτ, MulAut.one_apply]
    set b := a * τ a with hb
    have hb1 : τ b = b := by
      rw [hb, map_mul, hττ, hcomm]
    have hb2 : (τ * γ) b = b := by
      rw [hb, MulAut.mul_apply, map_mul, map_mul, ha, hτγτ, hγi, hcomm]
    have hb0 := hboth b hb1 hb2
    have hτa : τ a = a := by
      have e1 : τ a = a⁻¹ := eq_inv_of_mul_eq_one_right (by rw [← hb]; exact hb0)
      rw [e1, inv_eq_of_mul_eq_one_right (hsq a)]
    rw [Subgroup.mem_bot]
    exact hboth a hτa (by rw [MulAut.mul_apply, ha, hτa])
  have hvJ : v ∉ kerIn (M ⊓ I) I := fun hJ => hvB ⟨hJ, hvV⟩
  have hwJ : w ∉ kerIn (M ⊓ I) I := by
    intro hJ
    apply hvJ
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_kerIn (M ⊓ I) I hg) w).mp hJ
    convert this using 1
    rw [hw]
    group
  have hrefl : ∀ x : I, (x : Γ) * x = 1 → (x : Γ) ∉ kerIn (M ⊓ I) I →
      ∃ i, e (q x) = DihedralGroup.sr i := by
    intro x hx2 hxJ
    refine exists_eq_sr hodd ?_ ?_
    · rw [← map_mul, ← map_mul, show x * x = 1 from Subtype.ext hx2, map_one, map_one]
    · intro h1
      apply hxJ
      have : q x = 1 := e.injective (by rw [h1, map_one])
      rwa [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
  obtain ⟨i₁, hi₁⟩ := hrefl t hv2 hvJ
  obtain ⟨i₂, hi₂⟩ := hrefl ⟨w, hwI⟩ hw2 hwJ
  have heqc : e (q c) = DihedralGroup.sr i₁ * DihedralGroup.sr i₂ := by
    rw [show c = t * ⟨w, hwI⟩ from rfl, map_mul, map_mul, hi₁, hi₂]
  have hγp : γ ^ p = 1 := by
    rw [hγdef, ← map_pow]
    apply hker
    apply e.injective
    rw [map_pow, map_pow, heqc, sr_mul_sr_pow, map_one]
  have hQ : ∃ a : ↥P' ⧸ Z'.subgroupOf P', a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective ((kerIn (M ⊓ I) I).subgroupOf I)
      (e.symm (DihedralGroup.r 1))
    have hy' : q y = e.symm (DihedralGroup.r 1) := hy
    have hρy : ρ y = 1 := by
      ext a
      exact (hcon _).trans (hcon _).symm
    rw [hρ, conjSecAut_eq_one_iff] at hρy
    obtain ⟨n, hn⟩ := Ch3E213M.isTwo_of_centralizes hpr hcharI y.2 hρy
    have hn' : y ^ 2 ^ n = 1 := Subtype.ext (by simpa using hn)
    have h2 := congrArg (fun x => e (q x)) hn'
    simp only [map_pow, map_one] at h2
    rw [hy', MulEquiv.apply_symm_apply] at h2
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [DihedralGroup.orderOf_r_one] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3))
  have hγ1 : γ ≠ 1 := by
    intro h1
    obtain ⟨a, ha⟩ := hQ
    apply ha
    have : a ∈ fixSub γ := by rw [mem_fixSub, h1, MulAut.one_apply]
    rw [hfree] at this
    exact Subgroup.mem_bot.1 this
  have hγord : orderOf γ = p := orderOf_eq_prime hγp hγ1
  letI : CommGroup (↥P' ⧸ Z'.subgroupOf P') :=
    { (inferInstance : Group (↥P' ⧸ Z'.subgroupOf P')) with mul_comm := hcomm }
  obtain ⟨r, U, hU, hUsup, hUind⟩ := exists_decomp hsq hp hp2 hγord hτ hτγ hfree
  haveI hr : Nonempty (Fin r) := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      subst h0
      obtain ⟨a, ha⟩ := hQ
      apply ha
      have : a ∈ (⨆ i, U i) := by rw [hUsup]; exact Subgroup.mem_top a
      rw [iSup_of_empty] at this
      exact Subgroup.mem_bot.1 this
    · exact ⟨⟨0, h0⟩⟩
  have hcl : Subgroup.closure ((V : Set Γ) ∪ (B6.conjSub g⁻¹ V : Set Γ)) = I := by
    rw [← Subgroup.sup_eq_closure, ← hgen']
  have hρU' : ∀ i, ∀ z ∈ Subgroup.closure ((V : Set Γ) ∪ (B6.conjSub g⁻¹ V : Set Γ)),
      ∀ (hz : z ∈ I), ∀ u ∈ U i, ρ ⟨z, hz⟩ u ∈ U i := by
    intro i z hz'
    induction hz' using Subgroup.closure_induction with
    | mem x hx =>
      intro hxI u hu
      rcases hx with hx | hx
      · rcases hρV x hx with h1 | h1
        · rw [show (⟨x, hxI⟩ : I) = ⟨x, hpr.V_le hx⟩ from rfl, h1, MulAut.one_apply]
          exact hu
        · rw [show (⟨x, hxI⟩ : I) = ⟨x, hpr.V_le hx⟩ from rfl, h1]
          exact (hU i).2.1 u hu
      · rcases hρVg x hx with h1 | h1
        · rw [show (⟨x, hxI⟩ : I) = ⟨x, hpr.conj_le hx⟩ from rfl, h1, MulAut.one_apply]
          exact hu
        · rw [show (⟨x, hxI⟩ : I) = ⟨x, hpr.conj_le hx⟩ from rfl, h1, MulAut.mul_apply]
          exact (hU i).2.1 _ ((hU i).1 u hu)
    | one =>
      intro h1I u hu
      rw [show (⟨1, h1I⟩ : I) = 1 from rfl, map_one, MulAut.one_apply]
      exact hu
    | mul x y hx hy ihx ihy =>
      intro hxyI u hu
      have hxI : x ∈ I := by rw [← hcl]; exact hx
      have hyI : y ∈ I := by rw [← hcl]; exact hy
      rw [show (⟨x * y, hxyI⟩ : I) = ⟨x, hxI⟩ * ⟨y, hyI⟩ from rfl, map_mul, MulAut.mul_apply]
      exact ihx hxI _ (ihy hyI u hu)
    | inv x hx ihx =>
      intro hxI' u hu
      have hxI : x ∈ I := by rw [← hcl]; exact hx
      rw [show (⟨x⁻¹, hxI'⟩ : I) = (⟨x, hxI⟩ : I)⁻¹ from rfl, map_inv]
      exact inv_apply_mem (ihx hxI) u hu
  have hρU : ∀ i, ∀ z (hz : z ∈ I), ∀ u ∈ U i, ρ ⟨z, hz⟩ u ∈ U i :=
    fun i z hz => hρU' i z (by rw [hcl]; exact hz) hz
  refine ⟨r, fun i => liftSec (U i), fun i => ⟨le_liftSec hZP _, liftSec_le _, ?_, ?_⟩,
    iSup_liftSec U hUsup, fun i => ?_⟩
  ·
    show IsFaithfulIrredSection I (liftSec (U i)) Z' (kerIn (M ⊓ I) I)
    have hU0 : U i ≠ ⊥ := by
      intro h0
      have h1 := (hU i).2.2.1
      rw [h0, Subgroup.card_bot] at h1
      have hd' := dParamPrime_ne_zero hp hp2
      have h2 : (1 : ℕ) < 2 ^ (2 * E2.dParamPrime p) := Nat.one_lt_two_pow (by omega)
      omega
    have hWP : liftSec (U i) ≤ P' := liftSec_le _
    have hZW : Z' ≤ liftSec (U i) := le_liftSec hZP _
    have hIW : I ≤ Subgroup.normalizer (liftSec (U i) : Set Γ) := by
      have hfwd : ∀ x (hx : x ∈ I), ∀ y ∈ liftSec (U i), x * y * x⁻¹ ∈ liftSec (U i) := by
        intro x hx y hy
        obtain ⟨hyP, hyU⟩ := mem_liftSec.1 hy
        have hxyP : x * y * x⁻¹ ∈ P' := (Subgroup.mem_normalizer_iff.mp (hIP hx) y).mp hyP
        refine mem_liftSec.2 ⟨hxyP, ?_⟩
        have := hρU i x hx _ hyU
        rwa [hρ, conjSecAut_mk] at this
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => hfwd x hx y hy, fun hy => ?_⟩
      have := hfwd x⁻¹ (I.inv_mem hx) _ hy
      simpa [mul_assoc] using this
    refine ⟨lt_of_le_of_ne hZW ?_, hIW, hIZ,
      fun x hx y hy => (hpr.commutator_sq_mem_Z (hWP hx) (hWP hy)).1,
      fun x hx => (hpr.commutator_sq_mem_Z (hWP hx) (hWP hx)).2, ?_, ?_⟩
    ·
      intro hZW'
      apply hU0
      rw [eq_bot_iff]
      intro a ha
      obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective a
      have hyW : y ∈ liftSec (U i) := mem_liftSec.2 ⟨hy, ha⟩
      rw [← hZW'] at hyW
      exact Subgroup.mem_bot.2 ((QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hyW))
    ·
      intro Y hZY hYW hIY
      set Yt := (Y.subgroupOf P').map (QuotientGroup.mk' (Z'.subgroupOf P')) with hYt
      have hYtU : Yt ≤ U i := by
        rintro _ ⟨⟨y, hyP⟩, hy, rfl⟩
        obtain ⟨hy', hyU⟩ := mem_liftSec.1 (hYW (Subgroup.mem_subgroupOf.1 hy))
        exact hyU
      have hinv : ∀ (x : I), ∀ a ∈ Yt, ρ x a ∈ Yt := by
        rintro x _ ⟨⟨y, hyP⟩, hy, rfl⟩
        rw [QuotientGroup.mk'_apply, hρ, conjSecAut_mk]
        exact ⟨_, Subgroup.mem_subgroupOf.2 ((Subgroup.mem_normalizer_iff.mp (hIY x.2) y).mp
          (Subgroup.mem_subgroupOf.1 hy)), rfl⟩
      rcases (hU i).2.2.2 Yt hYtU (hinv c) (hinv t) with h0 | h0
      · left
        refine le_antisymm (fun y hy => ?_) hZY
        have hyP := (hYW.trans hWP) hy
        have hmem : ((⟨y, hyP⟩ : P') : ↥P' ⧸ Z'.subgroupOf P') ∈ Yt :=
          ⟨⟨y, hyP⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
        rw [h0, Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hmem
        exact hmem
      · right
        refine le_antisymm hYW fun x hx => ?_
        obtain ⟨hxP, hxU⟩ := mem_liftSec.1 hx
        rw [← h0] at hxU
        obtain ⟨⟨y, hyP⟩, hy, hyx⟩ := hxU
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hyx
        have := Y.mul_mem (Subgroup.mem_subgroupOf.1 hy) (hZY hyx)
        simpa using this
    ·
      intro x
      constructor
      · intro hx
        exact ⟨(kerIn_le.trans inf_le_right) hx,
          fun u hu => (hpr.commutator_sq_mem_Z (hJP x hx) (hWP hu)).1⟩
      · rintro ⟨hxI, hxc⟩
        by_contra hxJ
        have hfixU : ∀ a ∈ U i, ρ ⟨x, hxI⟩ a = a := by
          intro a ha
          obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective a
          exact (hfix ⟨x, hxI⟩ y hy).2 (hxc y (mem_liftSec.2 ⟨hy, ha⟩))
        let K : Subgroup I :=
          { carrier := {y | ∀ a ∈ U i, ρ y a = a}
            mul_mem' := fun {y y'} hy hy' a ha => by
              rw [map_mul, MulAut.mul_apply, hy' a ha, hy a ha]
            one_mem' := fun a _ => by rw [map_one, MulAut.one_apply]
            inv_mem' := fun {y} hy a ha => by
              rw [map_inv]
              conv_lhs => rw [← hy a ha]
              rw [MulAut.inv_apply_self] }
        have hKn : K.Normal := ⟨fun y hy z a ha => by
          have hza : ρ z⁻¹ a ∈ U i := hρU i _ (I.inv_mem z.2) a ha
          rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hy _ hza, ← MulAut.mul_apply,
            ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]⟩
        have hK'n : ((K.map q).map e.toMonoidHom).Normal :=
          (hKn.map q (QuotientGroup.mk'_surjective _)).map e.toMonoidHom e.surjective
        have hxK : e (q ⟨x, hxI⟩) ∈ (K.map q).map e.toMonoidHom :=
          ⟨q ⟨x, hxI⟩, ⟨⟨x, hxI⟩, hfixU, rfl⟩, rfl⟩
        have hx1 : e (q ⟨x, hxI⟩) ≠ 1 := by
          intro h1
          apply hxJ
          have : q ⟨x, hxI⟩ = 1 := e.injective (by rw [h1, map_one])
          rwa [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
            Subgroup.mem_subgroupOf] at this
        obtain ⟨_, ⟨y, hyK, rfl⟩, hy⟩ := r_one_mem_of_normal hp2 hK'n hxK hx1
        rw [MulEquiv.coe_toMonoidHom] at hy
        have hcm : q c = q (y ^ (i₂ - i₁).val) := by
          apply e.injective
          rw [heqc, DihedralGroup.sr_mul_sr, map_pow, map_pow, hy, DihedralGroup.r_one_pow,
            ZMod.natCast_zmod_val]
        have hρc : γ = ρ y ^ (i₂ - i₁).val := by rw [hγdef, hρq _ _ hcm, map_pow]
        apply hU0
        rw [eq_bot_iff]
        intro a ha
        have hγa : γ a = a := by
          rw [hρc]
          exact pow_apply_eq (hyK a ha) _
        have : a ∈ fixSub γ := hγa
        rw [hfree] at this
        exact this
  ·
    show E3.mQuot (liftSec (U i)) Z' = 2 * E2.dParamPrime p
    unfold E3.mQuot
    rw [relIndex_liftSec hZP, (hU i).2.2.1, padicValNat.prime_pow]
  ·
    show liftSec (U i) ⊓ ⨆ j, ⨆ (_ : j ≠ i), liftSec (U j) ≤ Z'
    calc liftSec (U i) ⊓ ⨆ j, ⨆ (_ : j ≠ i), liftSec (U j) ≤
        liftSec (U i) ⊓ liftSec (⨆ j, ⨆ (_ : j ≠ i), U j) :=
          inf_le_inf_left _ (iSup₂_le fun j hj => liftSec_mono (le_iSup₂_of_le j hj le_rfl))
      _ ≤ liftSec (U i ⊓ ⨆ j, ⨆ (_ : j ≠ i), U j) := liftSec_inf_le _ _
      _ = liftSec ⊥ := by rw [hUind i]
      _ ≤ Z' := liftSec_bot_le

end CFSG.Quasithin.SimsE2
