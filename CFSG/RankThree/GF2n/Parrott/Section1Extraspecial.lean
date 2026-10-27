module

public import CFSG.LargeExtraspecial.Timmesfeld.FStar
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.CoprimeDecomp
public import CFSG.Foundations.MaxCardThompson

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

private abbrev centreImage (J : Subgroup H) : Subgroup H :=
  (Subgroup.center J).map J.subtype

private abbrev centralizerIn (P J : Subgroup H) : Subgroup H :=
  J ⊓ Subgroup.centralizer (P : Set H)

private lemma card_centreImage {J : Subgroup H} (hJ : IsExtraspecial2 J) :
    Nat.card (centreImage J) = 2 := by
  change Nat.card ((Subgroup.center J).map J.subtype) = 2
  rw [← hJ.2.1]
  exact hJ.2.2

private lemma centreImage_le {J : Subgroup H} : centreImage J ≤ J :=
  Subgroup.map_subtype_le _

private lemma centreImage_le_centralizer (J : Subgroup H) :
    centreImage J ≤ Subgroup.centralizer (J : Set H) := by
  rintro z ⟨w, hw, rfl⟩
  exact Subgroup.mem_centralizer_iff.mpr fun y _hy =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨y, _hy⟩)

private lemma inf_centralizer_eq_centreImage (J : Subgroup H) :
    J ⊓ Subgroup.centralizer (J : Set H) = centreImage J :=
  (CFSG.center_map_subtype_eq_inf_centralizer J).symm

private lemma normalizer_le_normalizer_centreImage (J : Subgroup H) :
    Subgroup.normalizer (J : Set H) ≤ Subgroup.normalizer (centreImage J : Set H) := by
  have step : ∀ (m : H), m ∈ Subgroup.normalizer (J : Set H) → ∀ (j : ↥J),
      j ∈ Subgroup.center J → m * (j : H) * m⁻¹ ∈ centreImage J := by
    intro m hm j hj
    rw [Subgroup.mem_normalizer_iff] at hm
    have hm' : m⁻¹ ∈ Subgroup.normalizer (J : Set H) :=
      (Subgroup.normalizer (J : Set H)).inv_mem hm
    rw [Subgroup.mem_normalizer_iff] at hm'
    have hmj : m * (j : H) * m⁻¹ ∈ J := (hm (j : H)).mp j.2
    refine ⟨⟨m * (j : H) * m⁻¹, hmj⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr ?_
    intro y
    have hmy : m⁻¹ * (y : H) * m ∈ J := by
      simpa using (hm' (y : H)).mp y.2
    have hcomm : (⟨m⁻¹ * (y : H) * m, hmy⟩ : ↥J) * j =
        j * ⟨m⁻¹ * (y : H) * m, hmy⟩ := Subgroup.mem_center_iff.mp hj _
    have hcommH : (m⁻¹ * (y : H) * m) * (j : H) =
        (j : H) * (m⁻¹ * (y : H) * m) := congrArg Subtype.val hcomm
    apply Subtype.ext
    calc
      y * (m * (j : H) * m⁻¹) = m * ((m⁻¹ * (y : H) * m) * (j : H)) * m⁻¹ := by group
      _ = m * ((j : H) * (m⁻¹ * (y : H) * m)) * m⁻¹ := by rw [hcommH]
      _ = (m * (j : H) * m⁻¹) * y := by group
  intro n hn
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro z
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact step n hn j hj
  · intro hz
    rcases hz with ⟨j, hj, hjeq⟩
    have hn' : n⁻¹ ∈ Subgroup.normalizer (J : Set H) :=
      (Subgroup.normalizer (J : Set H)).inv_mem hn
    have hzj : n⁻¹ * (j : H) * n ∈ centreImage J := by
      simpa using step n⁻¹ hn' j hj
    have hz_eq : z = n⁻¹ * (j : H) * n := by
      calc
        z = n⁻¹ * (n * z * n⁻¹) * n := by group
        _ = n⁻¹ * (j : H) * n := by
          rw [← hjeq]
          rfl
    rw [hz_eq]
    exact hzj

private lemma normalizer_le_centralizer_of_card_two {Z : Subgroup H} (hZ : Nat.card Z = 2) :
    Subgroup.normalizer (Z : Set H) ≤ Subgroup.centralizer (Z : Set H) := by
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hconj : n * z * n⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hn z).mp hz
  by_cases hz1 : z = 1
  · subst hz1
    group
  · obtain ⟨t, ht_ne, ht_unique⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
    have hz_eq : (⟨z, hz⟩ : Z) = t :=
      ht_unique ⟨z, hz⟩ (by simpa using hz1)
    have hconj_ne : (⟨n * z * n⁻¹, hconj⟩ : Z) ≠ 1 := by
      intro h
      have h1 : n * z * n⁻¹ = 1 := congrArg Subtype.val h
      have hz1' : z = 1 := by
        have := congrArg (fun x => n⁻¹ * x * n) h1
        simpa [mul_assoc] using this
      exact hz1 hz1'
    have hconj_eq : (⟨n * z * n⁻¹, hconj⟩ : Z) = t :=
      ht_unique ⟨n * z * n⁻¹, hconj⟩ hconj_ne
    have hconjH : n * z * n⁻¹ = z := by
      have h1 : n * z * n⁻¹ = (t : H) := congrArg Subtype.val hconj_eq
      have h2 : z = (t : H) := congrArg Subtype.val hz_eq
      exact h1.trans h2.symm
    calc
      z * n = (n * z * n⁻¹) * n := by rw [hconjH]
      _ = n * z := by group

private lemma normalizer_le_centralizer_centreImage {J : Subgroup H} (hJ : IsExtraspecial2 J) :
    Subgroup.normalizer (J : Set H) ≤ Subgroup.centralizer (centreImage J : Set H) :=
  (normalizer_le_normalizer_centreImage J).trans
    (normalizer_le_centralizer_of_card_two (card_centreImage hJ))

private lemma commutator_centreImage_normalizer {J P : Subgroup H} (hJ : IsExtraspecial2 J)
    (hNP : P ≤ Subgroup.normalizer (J : Set H)) :
    ⁅centreImage J, P⁆ = ⊥ := by
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hNP.trans (normalizer_le_centralizer_centreImage hJ)

private lemma sup_centralizer_commutator_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {J P : Subgroup H} (hJ : IsExtraspecial2 J) (hP : IsPGroup p P)
    (hNP : P ≤ Subgroup.normalizer (J : Set H)) :
    centralizerIn P J ⊔ ⁅P, J⁆ = J := by
  refine le_antisymm ?_ ?_
  · refine sup_le inf_le_left ?_
    simpa only [Subgroup.commutator_comm] using
      (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.commutator_le_of_normalizer
        (Y := J) (B := P) hNP)
  · letI : Fact p.Prime := ⟨hp⟩
    have hcop : Nat.Coprime p (Nat.card J) := by
      letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨n, hn⟩ := hJ.1.exists_card_eq
      rw [hn]
      refine Nat.prime_two.coprime_pow_of_not_dvd (a := p) (m := n) ?_
      intro h2p
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p).symm
    have h := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.le_sup_centralizer_commutator
      (X := H) (p := p) (Y := J) (B := P) hP hNP hcop
    simpa only [centralizerIn, Subgroup.commutator_comm] using h

private lemma commutator_centralizer_commutator_eq_bot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {J P : Subgroup H} (hJ : IsExtraspecial2 J) (hP : IsPGroup p P)
    (hNP : P ≤ Subgroup.normalizer (J : Set H)) :
    ⁅centralizerIn P J, ⁅P, J⁆⁆ = ⊥ := by
  set C : Subgroup H := centralizerIn P J
  set K : Subgroup H := ⁅P, J⁆
  have hC_le_J : C ≤ J := inf_le_left
  have hJC_le_Z : ⁅J, C⁆ ≤ centreImage J := by
    calc
      ⁅J, C⁆ ≤ ⁅J, J⁆ := Subgroup.commutator_mono le_rfl hC_le_J
      _ = centreImage J := hJ.2.1
  have h1 : ⁅⁅J, C⁆, P⁆ = ⊥ := by
    have hle : ⁅⁅J, C⁆, P⁆ ≤ ⁅centreImage J, P⁆ :=
      Subgroup.commutator_mono hJC_le_Z le_rfl
    exact le_bot_iff.mp (by simpa only [commutator_centreImage_normalizer hJ hNP] using hle)
  have h2 : ⁅⁅C, P⁆, J⁆ = ⊥ := by
    have hCP : ⁅C, P⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact inf_le_right
    rw [hCP]
    simp
  have hKC : ⁅⁅P, J⁆, C⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := P) (H₂ := J) (H₃ := C) h1 h2
  simpa only [C, K, Subgroup.commutator_comm] using hKC

private lemma le_normalizer_commutator {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {J P : Subgroup H} (hJ : IsExtraspecial2 J) (hP : IsPGroup p P)
    (hNP : P ≤ Subgroup.normalizer (J : Set H)) :
    J ≤ Subgroup.normalizer ((⁅P, J⁆ : Subgroup H) : Set H) := by
  set C : Subgroup H := centralizerIn P J
  set K : Subgroup H := ⁅P, J⁆
  have hC_le_J : C ≤ J := inf_le_left
  have hCK : ⁅C, K⁆ = ⊥ := commutator_centralizer_commutator_eq_bot hp hp2 hJ hP hNP
  have hC_le_centK : C ≤ Subgroup.centralizer (K : Set H) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hCK
  have hCnorm : C ≤ Subgroup.normalizer (K : Set H) :=
    hC_le_centK.trans (Subgroup.centralizer_le_normalizer (K : Set H))
  have hKnorm : K ≤ Subgroup.normalizer (K : Set H) := Subgroup.le_normalizer
  have hsup : C ⊔ K = J := sup_centralizer_commutator_eq hp hp2 hJ hP hNP
  calc
    J = C ⊔ K := hsup.symm
    _ ≤ Subgroup.normalizer (K : Set H) := sup_le hCnorm hKnorm

private lemma centreImage_le_commutator {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {J P : Subgroup H} (hJ : IsExtraspecial2 J) (hP : IsPGroup p P)
    (hNP : P ≤ Subgroup.normalizer (J : Set H)) (hKne : ⁅P, J⁆ ≠ ⊥) :
    centreImage J ≤ ⁅P, J⁆ := by
  set C : Subgroup H := centralizerIn P J
  set K : Subgroup H := ⁅P, J⁆
  have hK_le_J : K ≤ J := by
    simpa only [K, Subgroup.commutator_comm] using
      (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.commutator_le_of_normalizer
        (Y := J) (B := P) hNP)
  have hJnormK : J ≤ Subgroup.normalizer (K : Set H) := le_normalizer_commutator hp hp2 hJ hP hNP
  have hKJ_le_K : ⁅K, J⁆ ≤ K :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.commutator_le_of_normalizer
      (Y := K) (B := J) hJnormK
  have hKJ_le_Z : ⁅K, J⁆ ≤ centreImage J := by
    calc
      ⁅K, J⁆ ≤ ⁅J, J⁆ := Subgroup.commutator_mono hK_le_J le_rfl
      _ = centreImage J := hJ.2.1
  have hZK_ne_bot : centreImage J ⊓ K ≠ ⊥ := by
    intro hbot
    have hKJ_bot : ⁅K, J⁆ = ⊥ := by
      refine le_bot_iff.mp ?_
      calc
        ⁅K, J⁆ ≤ K ⊓ centreImage J := le_inf hKJ_le_K hKJ_le_Z
        _ = ⊥ := by simpa only [inf_comm] using hbot
    have hK_le_centJ : K ≤ Subgroup.centralizer (J : Set H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKJ_bot
    have hK_le_Z : K ≤ centreImage J := by
      calc
        K ≤ J ⊓ Subgroup.centralizer (J : Set H) := le_inf hK_le_J hK_le_centJ
        _ = centreImage J := inf_centralizer_eq_centreImage J
    apply hKne
    refine le_bot_iff.mp ?_
    calc
      K ≤ K ⊓ centreImage J := le_inf le_rfl hK_le_Z
      _ = ⊥ := by simpa only [inf_comm] using hbot
  have hcard_dvd : Nat.card ((centreImage J ⊓ K : Subgroup H)) ∣
      Nat.card (centreImage J) :=
    Subgroup.card_dvd_of_le inf_le_left
  rw [card_centreImage hJ] at hcard_dvd
  have hcard_ne_one : Nat.card ((centreImage J ⊓ K : Subgroup H)) ≠ 1 := by
    intro h1
    exact hZK_ne_bot ((Subgroup.eq_bot_iff_card (H := (centreImage J ⊓ K))).mpr h1)
  have hcard_eq_two : Nat.card ((centreImage J ⊓ K : Subgroup H)) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hcard_dvd with h | h
    · exact absurd h hcard_ne_one
    · exact h
  have hEq : centreImage J ⊓ K = centreImage J :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [card_centreImage hJ, hcard_eq_two])
  simpa only [hEq] using (inf_le_right : centreImage J ⊓ K ≤ K)

private lemma isExtraspecial2_of_centre_eq {J L : Subgroup H} (hJ : IsExtraspecial2 J)
    (hL_le_J : L ≤ J) (hZL : centreImage J ≤ L)
    (hcenter : (Subgroup.center L).map L.subtype = centreImage J) (hLne : L ≠ centreImage J) :
    IsExtraspecial2 L := by
  have hLp : IsPGroup 2 L := hJ.1.to_le hL_le_J
  have hLL_le_Z : ⁅L, L⁆ ≤ centreImage J := by
    calc
      ⁅L, L⁆ ≤ ⁅J, J⁆ := Subgroup.commutator_mono hL_le_J hL_le_J
      _ = centreImage J := hJ.2.1
  have hLL_ne_bot : ⁅L, L⁆ ≠ ⊥ := by
    intro hbot
    apply hLne
    have hcomm : IsMulCommutative L :=
      Subgroup.commutator_self_eq_bot_iff.mp hbot
    have htop : Subgroup.center L = ⊤ := Subgroup.center_eq_top
    rw [htop] at hcenter
    have hmap : (⊤ : Subgroup ↥L).map L.subtype = L := by
      simpa using Subgroup.subgroupOf_map_subtype (⊤ : Subgroup H) L
    rw [← hmap]
    exact hcenter
  have hcard_dvd : Nat.card ((⁅L, L⁆ : Subgroup H)) ∣ Nat.card (centreImage J) :=
    Subgroup.card_dvd_of_le hLL_le_Z
  rw [card_centreImage hJ] at hcard_dvd
  have hcard_gt_one : 1 < Nat.card ((⁅L, L⁆ : Subgroup H)) :=
    (Subgroup.one_lt_card_iff_ne_bot (H := ⁅L, L⁆)).mpr hLL_ne_bot
  have hcard_LL : Nat.card ((⁅L, L⁆ : Subgroup H)) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hcard_dvd with h | h
    · omega
    · exact h
  have hLL_eq : ⁅L, L⁆ = centreImage J :=
    Subgroup.eq_of_le_of_card_ge hLL_le_Z (by rw [card_centreImage hJ, hcard_LL])
  refine ⟨hLp, ?_, ?_⟩
  · rw [hLL_eq]
    exact hcenter.symm
  · rw [hLL_eq, card_centreImage hJ]

private lemma center_centralizer_eq_centreImage {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {J P : Subgroup H} (hJ : IsExtraspecial2 J) (hP : IsPGroup p P)
    (hNP : P ≤ Subgroup.normalizer (J : Set H)) :
    (Subgroup.center (centralizerIn P J)).map (centralizerIn P J).subtype = centreImage J := by
  set C : Subgroup H := centralizerIn P J
  set K : Subgroup H := ⁅P, J⁆
  have hC_le_J : C ≤ J := inf_le_left
  have hCK : ⁅C, K⁆ = ⊥ := commutator_centralizer_commutator_eq_bot hp hp2 hJ hP hNP
  have hC_le_centK : C ≤ Subgroup.centralizer (K : Set H) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hCK
  have hsup : C ⊔ K = J := sup_centralizer_commutator_eq hp hp2 hJ hP hNP
  have hZ_le_C : centreImage J ≤ C := by
    refine le_inf (centreImage_le) ?_
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (commutator_centreImage_normalizer hJ hNP)
  refine le_antisymm ?_ ?_
  · intro x hx
    rcases hx with ⟨c, hc, rfl⟩
    have hcC : (c : H) ∈ C := c.2
    have hc_centC : c ∈ Subgroup.center C := hc
    have hC_le_centc : C ≤ Subgroup.centralizer ({(c : H)} : Set H) := by
      intro d hd
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc_centC ⟨d, hd⟩)
    have hK_le_centc : K ≤ Subgroup.centralizer ({(c : H)} : Set H) := by
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (hC_le_centK hcC) k hk
    have hJ_le_centc : J ≤ Subgroup.centralizer ({(c : H)} : Set H) := by
      rw [← hsup]
      exact sup_le hC_le_centc hK_le_centc
    have hcJ : (c : H) ∈ J := hC_le_J hcC
    have hc_centJ : (c : H) ∈ Subgroup.centralizer (J : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact Subgroup.mem_centralizer_singleton_iff.mp (hJ_le_centc hj)
    exact (by
      rw [← inf_centralizer_eq_centreImage J]
      exact ⟨hcJ, hc_centJ⟩)
  · intro z hz
    have hzC : z ∈ C := hZ_le_C hz
    refine ⟨⟨z, hzC⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr ?_
    intro d
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (centreImage_le_centralizer J hz) (d : H)
      (hC_le_J d.2)

private lemma centreImage_le_centralizerIn {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {J P : Subgroup H} (hJ : IsExtraspecial2 J) (hP : IsPGroup p P)
    (hNP : P ≤ Subgroup.normalizer (J : Set H)) :
    centreImage J ≤ centralizerIn P J :=
  le_inf centreImage_le
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (commutator_centreImage_normalizer hJ hNP))

private lemma commutator_le {J P : Subgroup H}
    (hNP : P ≤ Subgroup.normalizer (J : Set H)) : ⁅P, J⁆ ≤ J := by
  simpa only [Subgroup.commutator_comm] using
    (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.commutator_le_of_normalizer
      (Y := J) (B := P) hNP)

private lemma commutator_ne_bot_of_not_centralizes {J P : Subgroup H}
    (hnot : ¬ P ≤ Subgroup.centralizer (J : Set H)) : ⁅P, J⁆ ≠ ⊥ := by
  intro hbot
  exact hnot (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)

private lemma commutator_ne_centreImage_of_not_centralizes {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {J P : Subgroup H} (hJ : IsExtraspecial2 J) (hP : IsPGroup p P)
    (hNP : P ≤ Subgroup.normalizer (J : Set H))
    (hnot : ¬ P ≤ Subgroup.centralizer (J : Set H)) :
    ⁅P, J⁆ ≠ centreImage J := by
  intro hKZ
  apply hnot
  have hZ_le_C : centreImage J ≤ centralizerIn P J :=
    centreImage_le_centralizerIn hp hp2 hJ hP hNP
  have hJeq : J = centralizerIn P J ⊔ centreImage J :=
    (sup_centralizer_commutator_eq hp hp2 hJ hP hNP).symm.trans
      (congrArg (fun X => centralizerIn P J ⊔ X) hKZ)
  have hJC : J ≤ centralizerIn P J :=
    hJeq.le.trans (sup_le le_rfl hZ_le_C)
  have hJC' : J ≤ Subgroup.centralizer (P : Set H) := hJC.trans inf_le_right
  exact (Subgroup.le_centralizer_iff (H := J) (K := P)).mp hJC'

private lemma center_commutator_eq_centreImage {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {J P : Subgroup H} (hJ : IsExtraspecial2 J) (hP : IsPGroup p P)
    (hNP : P ≤ Subgroup.normalizer (J : Set H)) (hKne : ⁅P, J⁆ ≠ ⊥) :
    (Subgroup.center ((⁅P, J⁆ : Subgroup H))).map
      ((⁅P, J⁆ : Subgroup H)).subtype = centreImage J := by
  set C : Subgroup H := centralizerIn P J
  set K : Subgroup H := ⁅P, J⁆
  have hC_le_J : C ≤ J := inf_le_left
  have hK_le_J : K ≤ J := commutator_le hNP
  have hCK : ⁅C, K⁆ = ⊥ := commutator_centralizer_commutator_eq_bot hp hp2 hJ hP hNP
  have hC_le_centK : C ≤ Subgroup.centralizer (K : Set H) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hCK
  have hsup : C ⊔ K = J := sup_centralizer_commutator_eq hp hp2 hJ hP hNP
  have hZ_le_K : centreImage J ≤ K := centreImage_le_commutator hp hp2 hJ hP hNP hKne
  refine le_antisymm ?_ ?_
  · intro x hx
    rcases hx with ⟨k, hk, rfl⟩
    have hkK : (k : H) ∈ K := k.2
    have hk_centK : k ∈ Subgroup.center K := hk
    have hK_le_centk : K ≤ Subgroup.centralizer ({(k : H)} : Set H) := by
      intro d hd
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hk_centK ⟨d, hd⟩)
    have hC_le_centk : C ≤ Subgroup.centralizer ({(k : H)} : Set H) := by
      intro c hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (hC_le_centK hc) k hkK).symm
    have hJ_le_centk : J ≤ Subgroup.centralizer ({(k : H)} : Set H) := by
      rw [← hsup]
      exact sup_le hC_le_centk hK_le_centk
    have hk_centJ : (k : H) ∈ Subgroup.centralizer (J : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact Subgroup.mem_centralizer_singleton_iff.mp (hJ_le_centk hj)
    rw [← inf_centralizer_eq_centreImage J]
    exact ⟨hK_le_J hkK, hk_centJ⟩
  · intro z hz
    have hzK : z ∈ K := hZ_le_K hz
    refine ⟨⟨z, hzK⟩, ?_, rfl⟩
    exact Subgroup.mem_center_iff.mpr (fun d => by
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (centreImage_le_centralizer J hz) (d : H)
        (hK_le_J d.2))

private lemma commutator_isExtraspecial2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {J P : Subgroup H} (hJ : IsExtraspecial2 J) (hP : IsPGroup p P)
    (hNP : P ≤ Subgroup.normalizer (J : Set H))
    (hnot : ¬ P ≤ Subgroup.centralizer (J : Set H)) :
    IsExtraspecial2 ⁅P, J⁆ := by
  have hKne : ⁅P, J⁆ ≠ ⊥ := commutator_ne_bot_of_not_centralizes hnot
  exact isExtraspecial2_of_centre_eq hJ (commutator_le hNP)
    (centreImage_le_commutator hp hp2 hJ hP hNP hKne)
    (center_commutator_eq_centreImage hp hp2 hJ hP hNP hKne)
    (commutator_ne_centreImage_of_not_centralizes hp hp2 hJ hP hNP hnot)

theorem prop5_centralizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {J P : Subgroup H} (hJ : IsExtraspecial2 J) (hP : IsPGroup p P) (hPne : P ≠ ⊥)
    (hNP : P ≤ Subgroup.normalizer (J : Set H)) :
    IsExtraspecial2 (J ⊓ Subgroup.centralizer (P : Set H)) ∨
      J ⊓ Subgroup.centralizer (P : Set H) = (Subgroup.center J).map J.subtype := by
  by_cases hC : centralizerIn P J = centreImage J
  · right
    simpa only [centralizerIn, centreImage] using hC
  · left
    have h := isExtraspecial2_of_centre_eq hJ (L := centralizerIn P J) inf_le_left
      (centreImage_le_centralizerIn hp hp2 hJ hP hNP)
      (center_centralizer_eq_centreImage hp hp2 hJ hP hNP) hC
    simpa only [centralizerIn, centreImage] using h

theorem prop5_commutator_corrected {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {J P : Subgroup H} (hJ : IsExtraspecial2 J) (hP : IsPGroup p P) (hPne : P ≠ ⊥)
    (hNP : P ≤ Subgroup.normalizer (J : Set H)) :
    IsExtraspecial2 (⁅P, J⁆ : Subgroup H) ∨
      ⁅P, J⁆ = (Subgroup.center J).map J.subtype ∨ ⁅P, J⁆ = ⊥ := by
  by_cases hnot : ¬ P ≤ Subgroup.centralizer (J : Set H)
  · exact Or.inl (commutator_isExtraspecial2 hp hp2 hJ hP hNP hnot)
  · right
    right
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (not_not.mp hnot)

end CFSG.RankThree.GF2n.Parrott
