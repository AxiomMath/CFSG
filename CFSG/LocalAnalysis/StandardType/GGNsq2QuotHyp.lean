module

import Lean
public import CFSG.Mathlib.GroupTheory.CoprimeKernelLift
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoNormalizerLift

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.CoprimeKernel

namespace NsQuot

variable {G : Type} [Group G] [Finite G] {Q : Type} [Group Q]

@[expose] def img (N : Subgroup G) (f : ↥N →* Q) (U : Subgroup G) : Subgroup Q := (U.subgroupOf N).map f

theorem mem_img {N : Subgroup G} {f : ↥N →* Q} {U : Subgroup G} {q : Q} :
    q ∈ img N f U ↔ ∃ u : ↥N, (u : G) ∈ U ∧ f u = q := by
  simp [img, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem img_mono {N : Subgroup G} {f : ↥N →* Q} {U V : Subgroup G} (h : U ≤ V) :
    img N f U ≤ img N f V :=
  Subgroup.map_mono fun _ hx => h hx

theorem card_map_eq_of_inj {M : Type*} [Group M] {f : M →* Q} {U : Subgroup M}
    (hf : Function.Injective (fun u : U => f (u : M))) : Nat.card ↥(U.map f) = Nat.card ↥U :=
  (Nat.card_congr (Equiv.ofBijective (fun u : U => (⟨f u, u, u.2, rfl⟩ : ↥(U.map f)))
    ⟨fun a b h => hf (congrArg Subtype.val h),
     fun ⟨y, x, hx, hxy⟩ => ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩)).symm

structure Datum (p : ℕ) (N : Subgroup G) (f : ↥N →* Q) (L Bs Z : Subgroup G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  surj : Function.Surjective f
  ker_eq : f.ker = Z.subgroupOf N
  ZL : Z ≤ L
  LN : L ≤ N
  BsN : Bs ≤ N
  Zcent : ∀ z ∈ Z, ∀ l ∈ L, l * z = z * l
  Z2 : ∀ z ∈ Z, ∃ k : ℕ, z ^ (2 ^ k) = 1
  Bsp : ∀ b ∈ Bs, b ^ p = 1

variable {p : ℕ} {N : Subgroup G} {f : ↥N →* Q} {L Bs Z : Subgroup G}

theorem Datum.ZN (hD : Datum p N f L Bs Z) : Z ≤ N := hD.ZL.trans hD.LN

theorem Datum.mem_ker_iff (hD : Datum p N f L Bs Z) (n : ↥N) : n ∈ f.ker ↔ (n : G) ∈ Z := by
  rw [hD.ker_eq, Subgroup.mem_subgroupOf]

theorem Datum.ker_two (hD : Datum p N f L Bs Z) (k : ↥N) (hk : k ∈ f.ker) :
    ∃ m : ℕ, k ^ (2 ^ m) = 1 := by
  obtain ⟨m, hm⟩ := hD.Z2 k ((hD.mem_ker_iff k).1 hk)
  exact ⟨m, Subtype.ext (by simpa using hm)⟩

theorem Datum.isPGroup_ker (hD : Datum p N f L Bs Z) : IsPGroup 2 ↥f.ker := by
  intro k
  obtain ⟨m, hm⟩ := hD.ker_two k k.2
  exact ⟨m, Subtype.ext (by simpa using hm)⟩

theorem Datum.card_ker (hD : Datum p N f L Bs Z) : ∃ a : ℕ, Nat.card f.ker = 2 ^ a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (IsPGroup.iff_card).1 hD.isPGroup_ker

theorem Datum.not_dvd (hD : Datum p N f L Bs Z) : ¬ p ∣ Nat.card f.ker := by
  obtain ⟨a, ha⟩ := hD.card_ker
  intro h
  rw [ha] at h
  exact hD.odd ((Nat.prime_dvd_prime_iff_eq hD.prime Nat.prime_two).1 (hD.prime.dvd_of_dvd_pow h))

theorem Datum.isPGroup_sub (hD : Datum p N f L Bs Z) {U : Subgroup G} (hU : U ≤ Bs) :
    IsPGroup p ↥(U.subgroupOf N) := by
  intro x
  refine ⟨1, ?_⟩
  have hx : ((x : ↥N) : G) ∈ U := x.2
  have h1 : ((x : ↥N) : G) ^ p = 1 := hD.Bsp _ (hU hx)
  exact Subtype.ext (Subtype.ext (by simpa using h1))

theorem Datum.coprime (hD : Datum p N f L Bs Z) {U : Subgroup G} (hU : U ≤ Bs) :
    Nat.Coprime (Nat.card f.ker) (Nat.card (U.subgroupOf N)) := by
  haveI := Fact.mk hD.prime
  obtain ⟨a, ha⟩ := hD.card_ker
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 (hD.isPGroup_sub hU)
  rw [ha, hb]
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hD.prime).2 (Ne.symm hD.odd))

theorem Datum.injOn (hD : Datum p N f L Bs Z) {U : Subgroup G} (hU : U ≤ Bs) :
    Function.Injective (fun u : ↥(U.subgroupOf N) => f (u : ↥N)) :=
  injective_of_coprime (hD.coprime hU)

theorem Datum.card_img (hD : Datum p N f L Bs Z) {U : Subgroup G} (hU : U ≤ Bs) :
    Nat.card ↥(img N f U) = Nat.card ↥U := by
  unfold img
  rw [card_map_eq_of_inj (hD.injOn hU)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hU.trans hD.BsN)).toEquiv

theorem Datum.conj_mem (hD : Datum p N f L Bs Z) {n : G} (hn : n ∈ N) {z : G} (hz : z ∈ Z) :
    n * z * n⁻¹ ∈ Z := by
  have hk : (⟨z, hD.ZN hz⟩ : ↥N) ∈ f.ker := (hD.mem_ker_iff _).2 hz
  have h2 := (MonoidHom.normal_ker f).conj_mem _ hk ⟨n, hn⟩
  exact (hD.mem_ker_iff _).1 h2

theorem Datum.bstar (hD : Datum p N f L Bs Z) {B : Subgroup G} (hB : GGBstar p B Bs) :
    GGBstar p (img N f B) (img N f Bs) := by
  obtain ⟨hBBs, hel, hcard, hSC⟩ := hB
  refine ⟨img_mono hBBs, ⟨?_, ?_⟩, ?_, ?_⟩
  · refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨u, hu, hua⟩ := mem_img.1 a.2
    obtain ⟨v, hv, hvb⟩ := mem_img.1 b.2
    apply Subtype.ext
    show (a : Q) * b = b * a
    rw [← hua, ← hvb, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have h3 := hel.1.is_comm.comm (⟨(u : G), hu⟩ : ↥Bs) ⟨(v : G), hv⟩
    have h4 := congrArg Subtype.val h3
    exact h4
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := mem_img.1 hx
    rw [← map_pow]
    have h1 : ((u : ↥N) : G) ^ p = 1 := hD.Bsp _ hu
    have hu' : u ^ p = 1 := Subtype.ext (by simpa using h1)
    rw [hu', map_one]
  · rw [hD.card_img le_rfl, hD.card_img hBBs]
    exact hcard
  · intro g hgC hgp
    obtain ⟨n, rfl⟩ := hD.surj g
    haveI := Fact.mk hD.prime
    have hcomm : ∀ u ∈ Bs.subgroupOf N, f u * f n = f n * f u := by
      intro u hu
      have hmem : f u ∈ img N f Bs := mem_img.2 ⟨u, hu, rfl⟩
      exact Subgroup.mem_centralizer_iff.1 hgC (f u) hmem
    obtain ⟨n', hn'f, hn'c⟩ :=
      exists_lift_centralizing (hD.isPGroup_sub le_rfl) hD.not_dvd hcomm
    have hpow : (f n') ^ p = 1 := by rw [hn'f]; exact hgp
    obtain ⟨m, hm1, hm2⟩ := exists_pow_lift hD.prime hD.not_dvd hpow
    have hcent : ((n' ^ m : ↥N) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hbN : b ∈ N := hD.BsN hb
      have hc : Commute (⟨b, hbN⟩ : ↥N) n' := hn'c ⟨b, hbN⟩ hb
      exact congrArg Subtype.val (hc.pow_right m).eq
    have hp1 : ((n' ^ m : ↥N) : G) ^ p = 1 := by
      have := congrArg Subtype.val hm2
      simpa using this
    have hmemBs : ((n' ^ m : ↥N) : G) ∈ Bs := hSC _ hcent hp1
    refine mem_img.2 ⟨n' ^ m, hmemBs, ?_⟩
    rw [hm1, hn'f]

theorem Datum.cent (hD : Datum p N f L Bs Z) (hLperf : Group.IsPerfect ↥L) {B : Subgroup G}
    (hBBs : B ≤ Bs) :
    Nat.card ↥(img N f B ⊓ Subgroup.centralizer (img N f L : Set Q)) =
      Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := by
  haveI : Group.IsPerfect ↥(L.subgroupOf N) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hD.LN).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hD.LN).symm.surjective
  have hZL' : f.ker ≤ L.subgroupOf N := by
    intro k hk
    exact hD.ZL ((hD.mem_ker_iff k).1 hk)
  have hZc' : ∀ z ∈ f.ker, ∀ l ∈ L.subgroupOf N, l * z = z * l := by
    intro z hz l hl
    exact Subtype.ext (hD.Zcent _ ((hD.mem_ker_iff z).1 hz) _ hl)
  have hEq : img N f B ⊓ Subgroup.centralizer (img N f L : Set Q) =
      img N f (B ⊓ Subgroup.centralizer (L : Set G)) := by
    ext q
    constructor
    · intro hq
      obtain ⟨hqB, hqC⟩ := Subgroup.mem_inf.1 hq
      obtain ⟨b, hbB, rfl⟩ := mem_img.1 hqB
      refine mem_img.2 ⟨b, Subgroup.mem_inf.2 ⟨hbB, ?_⟩, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hcomm := commute_of_perfect (f := f) (L := L.subgroupOf N) inferInstance hZL' hZc'
        (b := b) (fun l' hl' => (Subgroup.mem_centralizer_iff.1 hqC (f l')
          (mem_img.2 ⟨l', hl', rfl⟩)).symm) ⟨l, hD.LN hl⟩ hl
      exact (congrArg Subtype.val hcomm).symm
    · intro hq
      obtain ⟨b, hbBC, rfl⟩ := mem_img.1 hq
      obtain ⟨hbB, hbC⟩ := Subgroup.mem_inf.1 hbBC
      refine Subgroup.mem_inf.2 ⟨mem_img.2 ⟨b, hbB, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro w hw
      obtain ⟨l, hl, rfl⟩ := mem_img.1 (SetLike.mem_coe.1 hw)
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1 hbC _ hl
  rw [hEq]
  exact hD.card_img (inf_le_left.trans hBBs)

end NsQuot

end CFSG.StandardType

end
