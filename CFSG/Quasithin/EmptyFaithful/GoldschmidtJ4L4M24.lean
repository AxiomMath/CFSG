module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4Alt8

public section

namespace CFSG.Quasithin.J4L4

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Open CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Ch1.SporLat.M24 (m24_overgroups m24Mems m24_card)

abbrev X24 : Type := ↥NativeSporadic.M24

theorem row_of_dvd : ∀ m ∈ m24Mems, 20160 ∣ m.order → m.order = 322560 ∧ m.o2 = 16 := by
  decide +kernel

theorem exists_mul_pCore
    {T B : Subgroup X24} (hT : IsSylowTwoOf T ⊤)
    (hTB : T ≤ Subgroup.normalizer (B : Set X24)) (g : ↥B →* alternatingGroup (Fin 8))
    (hg : Function.Surjective g) (hker : g.ker = CFSG.Open.pCore 2 ↥B) :
    ∀ t ∈ T, ∃ b ∈ B, b⁻¹ * t ∈ pCoreOf 2 (B ⊔ T) := by
  classical
  have hfin : Finite X24 := (CFSG.Sporadic.Mathieu.fam_m24_simplicity).1
  have hsimple : IsSimpleGroup X24 := (CFSG.Sporadic.Mathieu.fam_m24_simplicity).2.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup X24 := B ⊔ T with hY
  have hBY : B ≤ Y := le_sup_left
  have hTY : T ≤ Y := le_sup_right
  have hYB : Y ≤ Subgroup.normalizer (B : Set X24) := sup_le Subgroup.le_normalizer hTB
  have hcardB : Nat.card g.ker * 20160 = Nat.card B := by
    have := Subgroup.card_ker_mul_card_of_surjective hg
    rwa [card_alt8] at this
  have hkerP : IsPGroup 2 g.ker := by
    rw [hker]
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  have h20160 : 20160 ∣ Nat.card B := ⟨Nat.card g.ker, by rw [← hcardB]; ring⟩
  have hBYd : Nat.card B ∣ Nat.card Y := Subgroup.card_dvd_of_le hBY
  have hX : Nonempty (X24 ≃* NativeSporadic.Carrier .M24) := ⟨MulEquiv.refl _⟩
  rcases m24_overgroups hX hT hTY with htop | ⟨m, hm, hord, ho2, -⟩
  ·
    exfalso
    have hBn : B.Normal := Subgroup.normalizer_eq_top_iff.1 (eq_top_iff.2 (htop ▸ hYB))
    rcases hsimple.eq_bot_or_eq_top_of_normal B with hB | hB
    · rw [hB, Subgroup.card_bot] at h20160
      norm_num at h20160
    · have h1 : Nat.card B = 2 ^ 10 * 239085 := by
        rw [hB, Subgroup.card_top, m24_card]
      rw [h1] at hcardB
      obtain ⟨n, hn⟩ := hkerP.exists_card_eq
      rw [hn] at hcardB
      have h12144 : 2 ^ n = 12144 :=
        Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 20160) (by rw [hcardB]; norm_num)
      have h3 : 3 ∣ 2 ^ n := by
        rw [h12144]
        norm_num
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
  · have hdv : 20160 ∣ m.order := hord ▸ h20160.trans hBYd
    obtain ⟨hm1, hm2⟩ := row_of_dvd m hm hdv
    set Q : Subgroup X24 := pCoreOf 2 Y with hQ
    have hQcard : Nat.card Q = 16 := ho2.trans hm2
    have hQY : Q ≤ Y := pCoreOf_le 2 Y
    have hQn : Y ≤ Subgroup.normalizer (Q : Set X24) := le_normalizer_pCoreOf 2 Y
    set R : Subgroup X24 := pCoreOf 2 B with hR
    have hRB : R ≤ B := pCoreOf_le 2 B
    have hRn : Y ≤ Subgroup.normalizer (R : Set X24) := fun y hy =>
      normalizer_le_normalizer_pCoreOf 2 B (hYB hy)
    have hRQ : R ≤ Q := le_pCoreOf_of_le_normalizer 2 (hRB.trans hBY) hRn (pCoreOf_isPGroup 2 B)
    have hQBR : Q ⊓ B ≤ R := by
      refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
        ((pCoreOf_isPGroup 2 Y).to_le inf_le_left)
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro z
      simp only [Subgroup.mem_inf]
      exact and_congr (Subgroup.mem_normalizer_iff.1 (hQn (hBY hy)) z)
        (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hy) z)
    set Q' : Subgroup ↥Y := Q.subgroupOf Y with hQ'
    have hQ'n : Q'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQY).2 hQn
    let φ : ↥B →* ↥Y ⧸ Q' := (QuotientGroup.mk' Q').comp (Subgroup.inclusion hBY)
    have hkerφ : φ.ker = g.ker := by
      rw [hker]
      ext b
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      have hb : b ∈ CFSG.Open.pCore 2 ↥B ↔ (b : X24) ∈ R :=
        (Subgroup.mem_map_iff_mem B.subtype_injective).symm
      rw [hb]
      constructor
      · intro h
        exact hQBR ⟨h, b.2⟩
      · intro h
        exact hRQ h
    have hcardφ : Nat.card φ.range = 20160 := by
      have h1 := Subgroup.card_ker_mul_card_range φ
      rw [hkerφ] at h1
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans hcardB.symm)
    have hQ'card : Nat.card Q' = 16 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQY).toEquiv]
      exact hQcard
    have hYcard : Nat.card Y = 322560 := hord.trans hm1
    have hquot : Nat.card (↥Y ⧸ Q') = 20160 := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup Q'
      rw [hYcard, hQ'card] at this
      omega
    have htop' : φ.range = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hcardφ, hquot])
    intro t ht
    obtain ⟨b, hb⟩ : ∃ b : ↥B, φ b = ((⟨t, hTY ht⟩ : ↥Y) : ↥Y ⧸ Q') := by
      have : ((⟨t, hTY ht⟩ : ↥Y) : ↥Y ⧸ Q') ∈ φ.range := htop' ▸ Subgroup.mem_top _
      exact this
    refine ⟨b, b.2, ?_⟩
    have := QuotientGroup.eq.1 hb
    exact Subgroup.mem_subgroupOf.1 this

end CFSG.Quasithin.J4L4
