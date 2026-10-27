module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def quasiCentre (L : Subgroup G) : Subgroup G :=
  (Subgroup.center ↥L).map L.subtype

private lemma w183K3Quasi_mem_sup_of_centralizes {A B : Subgroup G}
    (hBA : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction'' with
  | mem y hy =>
      rw [Set.mem_union] at hy
      rcases hy with hy | hy
      · exact ⟨y, hy, 1, B.one_mem, mul_one y⟩
      · exact ⟨1, A.one_mem, y, hy, one_mul y⟩
  | inv_mem y hy =>
      rw [Set.mem_union] at hy
      rcases hy with hy | hy
      · exact ⟨y⁻¹, A.inv_mem hy, 1, B.one_mem, mul_one _⟩
      · exact ⟨1, A.one_mem, y⁻¹, B.inv_mem hy, one_mul _⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
  | mul y z _ _ ihy ihz =>
      obtain ⟨a, ha, b, hb, rfl⟩ := ihy
      obtain ⟨a', ha', b', hb', rfl⟩ := ihz
      refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
      rw [show (a * b) * (a' * b') = a * (b * a') * b' from by group, hBA b hb a' ha']
      group

private lemma w183K3Quasi_comm_comm_mul {x l l' : G}
    (h : (x * l' * x⁻¹ * l'⁻¹) * l = l * (x * l' * x⁻¹ * l'⁻¹)) :
    x * (l * l') * x⁻¹ * (l * l')⁻¹ =
      (x * l * x⁻¹ * l⁻¹) * (x * l' * x⁻¹ * l'⁻¹) := by
  have h1 : x * (l * l') * x⁻¹ * (l * l')⁻¹ =
      (x * l * x⁻¹) * (x * l' * x⁻¹) * l'⁻¹ * l⁻¹ := by
    rw [mul_inv_rev]; group
  rw [h1]
  conv_lhs =>
    rw [show x * l * x⁻¹ = (x * l * x⁻¹ * l⁻¹) * l from by group,
        show x * l' * x⁻¹ = (x * l' * x⁻¹ * l'⁻¹) * l' from by group]
  rw [show ((x * l * x⁻¹ * l⁻¹) * l) * ((x * l' * x⁻¹ * l'⁻¹) * l') * l'⁻¹ * l⁻¹
      = (x * l * x⁻¹ * l⁻¹) * (l * (x * l' * x⁻¹ * l'⁻¹)) * (l' * l'⁻¹ * l⁻¹) from by group]
  rw [← h]
  group

theorem quasiCentre_le (L : Subgroup G) : quasiCentre L ≤ L := by
  exact Subgroup.map_subtype_le _

theorem mem_quasiCentre {L : Subgroup G} {z : G} :
    z ∈ quasiCentre L ↔ z ∈ L ∧ ∀ l ∈ L, z * l = l * z := by
  rw [quasiCentre, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, fun l hl => ?_⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hx (⟨l, hl⟩ : ↥L))).symm
  · rintro ⟨hzL, hzcomm⟩
    exact ⟨⟨z, hzL⟩, Subgroup.mem_center_iff.mpr fun l => Subtype.ext (hzcomm l l.2).symm, rfl⟩

theorem quasi_commutator_eq {L : Subgroup G} (hL : CFSG.Open.IsQuasisimple ↥L) : ⁅L, L⁆ = L := by
  have hmap : Subgroup.map L.subtype (commutator ↥L) = ⁅L, L⁆ := by
    rw [show commutator ↥L = ⁅(⊤ : Subgroup ↥L), ⊤⁆ from rfl,
      Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [← hmap, hL.1, Subgroup.map_top, Subgroup.range_subtype]

theorem quasi_exists_noncomm {L : Subgroup G} (hL : CFSG.Open.IsQuasisimple ↥L) :
    ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hcomm : ⁅L, L⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (h a ha b hb).symm
  have hbot : L = ⊥ := (quasi_commutator_eq hL).symm.trans hcomm
  haveI : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hL.2.toNontrivial
  have hsub : Subsingleton ↥L := hbot.symm ▸ (inferInstance : Subsingleton ↥(⊥ : Subgroup G))
  have hsubq : Subsingleton (↥L ⧸ Subgroup.center ↥L) :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).subsingleton
  obtain ⟨a, b, hab⟩ := exists_pair_ne (↥L ⧸ Subgroup.center ↥L)
  exact hab (Subsingleton.elim a b)

theorem quasi_normal_dichotomy {L K : Subgroup G} (hL : CFSG.Open.IsQuasisimple ↥L) (hKL : K ≤ L)
    (hKn : ∀ y ∈ L, ∀ k ∈ K, y * k * y⁻¹ ∈ K) : K ≤ quasiCentre L ∨ K = L := by
  let K' : Subgroup ↥L := K.subgroupOf L
  have hK'normal : K'.Normal :=
    (Subgroup.normal_subgroupOf_iff hKL).mpr fun h k hh hk => hKn k hk h hh
  haveI : K'.Normal := hK'normal
  let Z : Subgroup ↥L := Subgroup.center ↥L
  let π : ↥L →* (↥L ⧸ Z) := QuotientGroup.mk' Z
  have hSnormal : (K'.map π).Normal := hK'normal.map π (QuotientGroup.mk'_surjective Z)
  haveI : (K'.map π).Normal := hSnormal
  haveI : IsSimpleGroup (↥L ⧸ Z) := hL.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K'.map π) with hS | hS
  · left
    intro k hk
    rw [mem_quasiCentre]
    refine ⟨hKL hk, fun l hl => ?_⟩
    have hk'Z : (⟨k, hKL hk⟩ : ↥L) ∈ Z := by
      have hmem : π (⟨k, hKL hk⟩ : ↥L) ∈ (⊥ : Subgroup (↥L ⧸ Z)) := by
        rw [← hS]
        exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hk)
      rw [Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff _).mp hmem
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hk'Z (⟨l, hl⟩ : ↥L))).symm
  · right
    apply le_antisymm hKL
    have hZcent : Z ≤ Subgroup.centralizer (K' : Set ↥L) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro k _
      exact Subgroup.mem_center_iff.mp hz k
    have hZK : ⁅Z, K'⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZcent
    have hKZ : ⁅K', Z⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hZK
    have hZZ : ⁅Z, Z⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun z hz =>
      Subgroup.mem_centralizer_iff.mpr fun w _ => Subgroup.mem_center_iff.mp hz w
    have hsup : K' ⊔ Z = ⊤ := by
      have h := Subgroup.comap_map_eq (f := π) K'
      rw [hS, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
      exact h.symm
    have htop_le : (⊤ : Subgroup ↥L) ≤ K' := by
      have hle : ⁅(⊤ : Subgroup ↥L), ⊤⁆ ≤ K' := by
        rw [show (⊤ : Subgroup ↥L) = K' ⊔ Z from hsup.symm,
          Subgroup.commutator_sup_left (K' ⊔ Z) K' Z,
          Subgroup.commutator_sup_right K' Z K',
          Subgroup.commutator_sup_right K' Z Z, hZK, hKZ, hZZ]
        simp only [sup_bot_eq]
        exact Subgroup.commutator_le_left K' K'
      rw [← hL.1]
      exact hle
    have hK'top : K' = ⊤ := le_antisymm le_top htop_le
    intro l hl
    have hmem : (⟨l, hl⟩ : ↥L) ∈ K' := by rw [hK'top]; trivial
    exact Subgroup.mem_subgroupOf.mp hmem

theorem quasi_comm_of_comm_mod_centre {L : Subgroup G} (hL : CFSG.Open.IsQuasisimple ↥L) {x : G}
    (hx : ∀ l ∈ L, x * l * x⁻¹ ∈ L) (h : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ quasiCentre L) :
    ∀ l ∈ L, x * l = l * x := by
  let f : ↥L →* ↥(Subgroup.center ↥L) :=
    { toFun := fun l =>
        ⟨⟨x * (l : G) * x⁻¹ * (l : G)⁻¹, (mem_quasiCentre.mp (h l l.2)).1⟩,
          Subgroup.mem_center_iff.mpr fun w =>
            Subtype.ext ((mem_quasiCentre.mp (h l l.2)).2 (w : G) w.2).symm⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_mul' := fun l l' => by
        apply Subtype.ext
        apply Subtype.ext
        exact w183K3Quasi_comm_comm_mul ((mem_quasiCentre.mp (h l' l'.2)).2 (l : G) l.2) }
  have htop : (⊤ : Subgroup ↥L) ≤ f.ker := by
    have hle : ⁅(⊤ : Subgroup ↥L), ⊤⁆ ≤ f.ker := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)
    rw [← hL.1]
    exact hle
  intro l hl
  have hfl : f (⟨l, hl⟩ : ↥L) = 1 := MonoidHom.mem_ker.mp (htop trivial)
  have hval : x * l * x⁻¹ * l⁻¹ = 1 := by
    have h1 : ((f (⟨l, hl⟩ : ↥L) : ↥(Subgroup.center ↥L)) : ↥L) = 1 := by
      rw [hfl]; rfl
    have h2 : (((f (⟨l, hl⟩ : ↥L) : ↥(Subgroup.center ↥L)) : ↥L) : G) = 1 := by
      rw [h1]; rfl
    exact h2
  have hconj : x * l * x⁻¹ = l := mul_inv_eq_one.mp hval
  calc x * l = (x * l * x⁻¹) * x := by group
    _ = l * x := by rw [hconj]

theorem quasi_centre_two_pow_eq_one {L : Subgroup G} [Finite ↥L]
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥L))) {z : G} (hz : z ∈ quasiCentre L) {k : ℕ}
    (hzk : z ^ (2 ^ k) = 1) : z = 1 := by
  rw [quasiCentre, Subgroup.mem_map] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  have hxpow : x ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hzk)
  have hcop : (orderOf x).Coprime (Nat.card ↥(Subgroup.center ↥L)) :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hxpow)
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd))
  have hx1 : x = 1 := orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd hcop (Subgroup.orderOf_dvd_natCard _ hx))
  exact congrArg Subtype.val hx1

theorem isPGroup_inf_odd_eq_bot {A N : Subgroup G} (hA : IsPGroup 2 A)
    (hN : Odd (Nat.card ↥N)) : A ⊓ N = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxA, hxN⟩ := hx
  obtain ⟨k, hk⟩ := hA ⟨x, hxA⟩
  have hxpow : x ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hcop : (orderOf x).Coprime (Nat.card ↥N) :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hxpow)
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hN))
  have hx1 : x = 1 := orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd hcop (Subgroup.orderOf_dvd_natCard N hxN))
  simpa using hx1

theorem commutator_perfect_of_central {F Z : Subgroup G} (hZc : ∀ z ∈ Z, ∀ f ∈ F, z * f = f * z)
    (h : F ≤ ⁅F, F⁆ ⊔ Z) : ⁅⁅F, F⁆, ⁅F, F⁆⁆ = ⁅F, F⁆ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    exact Subgroup.commutator_mem_commutator
      (by simpa using Subgroup.commutator_le_sup F F ha)
      (by simpa using Subgroup.commutator_le_sup F F hb)
  · rw [Subgroup.commutator_le]
    intro f hf f' hf'
    have hBA : ∀ b ∈ Z, ∀ a ∈ ⁅F, F⁆, b * a = a * b := fun b hb a ha =>
      hZc b hb a (by simpa using Subgroup.commutator_le_sup F F ha)
    obtain ⟨a, ha, z, hz, haz⟩ :=
      w183K3Quasi_mem_sup_of_centralizes (A := ⁅F, F⁆) (B := Z) hBA (h hf)
    obtain ⟨a', ha', z', hz', haz'⟩ :=
      w183K3Quasi_mem_sup_of_centralizes (A := ⁅F, F⁆) (B := Z) hBA (h hf')
    have haF : a ∈ F := by simpa using Subgroup.commutator_le_sup F F ha
    have ha'F : a' ∈ F := by simpa using Subgroup.commutator_le_sup F F ha'
    have hzF : z ∈ F := by
      have : z = a⁻¹ * f := by rw [← haz]; group
      rw [this]; exact F.mul_mem (F.inv_mem haF) hf
    have hz'F : z' ∈ F := by
      have : z' = a'⁻¹ * f' := by rw [← haz']; group
      rw [this]; exact F.mul_mem (F.inv_mem ha'F) hf'
    have hz_a' : ⁅z, a'⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hZc z hz a' ha'F)
    have hz_z' : ⁅z, z'⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hZc z hz z' hz'F)
    have ha_z' : ⁅a, z'⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hZc z' hz' a haF).symm
    rw [← haz, ← haz']
    have heq : ⁅a * z, a' * z'⁆ = ⁅a, a'⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_mul_right_eq_mul_conj, hz_a', hz_z', ha_z']
      group
    rw [heq]
    exact Subgroup.commutator_mem_commutator ha ha'

theorem isQuasisimple_of_central_simple_quot {F Z : Subgroup G} [(Z.subgroupOf F).Normal]
    (hF : ⁅F, F⁆ = F) (hZF : Z ≤ F) (hZc : ∀ z ∈ Z, ∀ f ∈ F, z * f = f * z)
    (hs : IsSimpleGroup (↥F ⧸ Z.subgroupOf F)) :
    CFSG.Open.IsQuasisimple ↥F ∧ quasiCentre F = Z := by
  let N : Subgroup ↥F := Z.subgroupOf F
  have hNcenter : N ≤ Subgroup.center ↥F := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro f
    exact Subtype.ext (hZc (z : G) (Subgroup.mem_subgroupOf.mp hz) (f : G) f.2).symm
  have hperfF : commutator ↥F = ⊤ := by
    apply Subgroup.map_injective F.subtype_injective
    have hmap : Subgroup.map F.subtype (commutator ↥F) = ⁅F, F⁆ := by
      rw [show commutator ↥F = ⁅(⊤ : Subgroup ↥F), ⊤⁆ from rfl,
        Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    rw [hmap, hF, Subgroup.map_top, Subgroup.range_subtype]
  haveI : IsSimpleGroup (↥F ⧸ N) := hs
  have hQperf : commutator (↥F ⧸ N) = ⊤ := by
    have h : Subgroup.map (QuotientGroup.mk' N) (commutator ↥F) = ⊤ := by
      rw [hperfF, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
    have h2 : Subgroup.map (QuotientGroup.mk' N) (commutator ↥F) = commutator (↥F ⧸ N) := by
      rw [show commutator ↥F = ⁅(⊤ : Subgroup ↥F), ⊤⁆ from rfl,
        Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)]
      rfl
    rw [← h2]; exact h
  have hSnormal : ((Subgroup.center ↥F).map (QuotientGroup.mk' N)).Normal :=
    (inferInstance : (Subgroup.center ↥F).Normal).map _ (QuotientGroup.mk'_surjective N)
  haveI : ((Subgroup.center ↥F).map (QuotientGroup.mk' N)).Normal := hSnormal
  have hcenter_le_N : Subgroup.center ↥F ≤ N := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((Subgroup.center ↥F).map (QuotientGroup.mk' N)) with hS | hS
    · intro x hx
      have hmem : QuotientGroup.mk' N x ∈ (⊥ : Subgroup (↥F ⧸ N)) := by
        rw [← hS]
        exact Subgroup.mem_map_of_mem _ hx
      rw [Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff _).mp hmem
    · exfalso
      have hcenter : Subgroup.center (↥F ⧸ N) = ⊤ := by
        have hle : (Subgroup.center ↥F).map (QuotientGroup.mk' N) ≤
            Subgroup.center (↥F ⧸ N) := by
          intro y hy
          obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
          rw [Subgroup.mem_center_iff]
          intro w
          obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective N w
          rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx v]
        exact top_le_iff.mp (hS.symm.trans_le hle)
      have hcomm : IsMulCommutative (↥F ⧸ N) := Subgroup.center_eq_top_iff.mp hcenter
      have hbot : commutator (↥F ⧸ N) = ⊥ := (commutator_eq_bot_iff (↥F ⧸ N)).mpr hcomm
      rw [hQperf] at hbot
      exact top_ne_bot hbot
  have hcenter_eq : Subgroup.center ↥F = N := le_antisymm hcenter_le_N hNcenter
  refine ⟨⟨hperfF, ?_⟩, ?_⟩
  · exact (MulEquiv.isSimpleGroup_congr
      (QuotientGroup.quotientMulEquivOfEq hcenter_eq)).mpr hs
  · rw [quasiCentre, hcenter_eq]
    change (Z.subgroupOf F).map F.subtype = Z
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZF]

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
