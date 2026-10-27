module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12
public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12Mixed
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofTypes
import CFSG.RankThree.PartTwo.Sec13.Item131Facts

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem exists_zpow_mul_of_card_nine {G : Type} [Group G] [Finite G] {P E : Subgroup G} {c b : G}
    (hc3 : orderOf c = 3) (hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hPE : P ≤ E) (hP : Nat.card P = 9) (hcP : c ∈ P) (hbP : b ∈ P)
    (hbZ : b ∉ Subgroup.zpowers c) :
    ∀ p ∈ P, ∃ k : ℤ, ∃ z ∈ Subgroup.zpowers c, p = b ^ k * z := by
  have hb1 : b ≠ 1 := fun h => hbZ (h ▸ one_mem _)
  have hbo : orderOf b = 3 := orderOf_eq_prime (hE3 b (hPE hbP)) hb1
  have hZcard : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hc3]
  have hBcard : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hbo]
  have hZP : Subgroup.zpowers c ≤ P := Subgroup.zpowers_le.mpr hcP
  have hBP : Subgroup.zpowers b ≤ P := Subgroup.zpowers_le.mpr hbP
  have hcomm : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ Subgroup.zpowers c, x * y = y * x := fun x hx y hy =>
    hEcomm x (hPE (hBP hx)) y (hPE (hZP hy))
  obtain ⟨hcardeq, hset⟩ :=
    CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.zpowers b) (Subgroup.zpowers c)
      hcomm
  have hinf : Nat.card (Subgroup.zpowers b ⊓ Subgroup.zpowers c : Subgroup G) = 1 := by
    have hdvd : Nat.card (Subgroup.zpowers b ⊓ Subgroup.zpowers c : Subgroup G) ∣ 3 := by
      rw [← hBcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact h
    · exfalso
      have heq : Subgroup.zpowers b ⊓ Subgroup.zpowers c = Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hBcard])
      exact hbZ (inf_eq_left.mp heq (Subgroup.mem_zpowers b))
  have hsup : Nat.card (Subgroup.zpowers b ⊔ Subgroup.zpowers c : Subgroup G) = 9 := by
    rw [hinf, hBcard, hZcard] at hcardeq
    omega
  have hPeq : Subgroup.zpowers b ⊔ Subgroup.zpowers c = P :=
    Subgroup.eq_of_le_of_card_ge (sup_le hBP hZP) (by rw [hsup, hP])
  intro p hp
  have hp' : p ∈ ((Subgroup.zpowers b ⊔ Subgroup.zpowers c : Subgroup G) : Set G) := by
    rw [hPeq]; exact hp
  rw [hset] at hp'
  obtain ⟨x, hx, z, hz, rfl⟩ := hp'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact ⟨k, z, hz, rfl⟩

theorem conj_commutator_mem_of_mixed {G : Type} [Group G] [Finite G] {E P₁ P₂ : Subgroup G}
    {c b t : G} (hc3 : orderOf c = 3) (hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hP₁E : P₁ ≤ E) (hP₂E : P₂ ≤ E) (hE : P₁ ⊔ P₂ = E)
    (hP₁ : Nat.card P₁ = 9) (hP₂ : Nat.card P₂ = 9) (hcP₁ : c ∈ P₁) (hcP₂ : c ∈ P₂)
    (hZ : P₁ ⊓ P₂ = Subgroup.zpowers c) (ht₁ : ∀ x ∈ P₁, t * x * t⁻¹ ∈ P₁)
    (ht₂ : ∀ x ∈ P₂, t * x * t⁻¹ ∈ P₂) (hbE : b ∈ E) (hb₁ : b ∉ P₁) (hb₂ : b ∉ P₂)
    (htb : t * b = b * t) :
    ∀ x ∈ E, t * x * t⁻¹ * x⁻¹ ∈ Subgroup.zpowers c := by
  set Z := Subgroup.zpowers c with hZdef
  have hZP₁ : Z ≤ P₁ := Subgroup.zpowers_le.mpr hcP₁
  have hZP₂ : Z ≤ P₂ := Subgroup.zpowers_le.mpr hcP₂
  have htZ : ∀ z ∈ Z, t * z * t⁻¹ ∈ Z := fun z hz => by
    rw [← hZ]
    exact ⟨ht₁ z (hZP₁ hz), ht₂ z (hZP₂ hz)⟩
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute P₁ P₂
    (fun x hx y hy => hEcomm x (hP₁E hx) y (hP₂E hy))).2
  have hbmem : b ∈ ((P₁ ⊔ P₂ : Subgroup G) : Set G) := by rw [hE]; exact hbE
  rw [hset] at hbmem
  obtain ⟨b₁, hb₁P, b₂, hb₂P, hbb⟩ := hbmem
  have hbb : b₁ * b₂ = b := hbb
  have hb₁P : b₁ ∈ P₁ := hb₁P
  have hb₂P : b₂ ∈ P₂ := hb₂P
  have hb₁Z : b₁ ∉ Z := fun h => hb₂ (by rw [← hbb]; exact mul_mem (hZP₂ h) hb₂P)
  have hb₂Z : b₂ ∉ Z := fun h => hb₁ (by rw [← hbb]; exact mul_mem hb₁P (hZP₁ h))
  have hu₁ : t * b₁ * t⁻¹ ∈ P₁ := ht₁ b₁ hb₁P
  have hu₂ : t * b₂ * t⁻¹ ∈ P₂ := ht₂ b₂ hb₂P
  have hu : t * b₁ * t⁻¹ * (t * b₂ * t⁻¹) = b₁ * b₂ := by
    calc t * b₁ * t⁻¹ * (t * b₂ * t⁻¹) = t * (b₁ * b₂) * t⁻¹ := by group
      _ = t * b * t⁻¹ := by rw [hbb]
      _ = b := by rw [htb]; group
      _ = b₁ * b₂ := hbb.symm
  have hw1 : b₁⁻¹ * (t * b₁ * t⁻¹) = b₂ * (t * b₂ * t⁻¹)⁻¹ := by
    have h1 : t * b₁ * t⁻¹ = b₁ * b₂ * (t * b₂ * t⁻¹)⁻¹ := by rw [← hu]; group
    rw [h1]; group
  have hwZ : b₁⁻¹ * (t * b₁ * t⁻¹) ∈ Z := by
    rw [← hZ]
    refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hb₁P) hu₁, ?_⟩
    rw [hw1]
    exact mul_mem hb₂P (inv_mem hu₂)
  set w := b₁⁻¹ * (t * b₁ * t⁻¹) with hwdef
  have hwb₁ : t * b₁ * t⁻¹ = b₁ * w := by rw [hwdef]; group
  have hwb₂ : t * b₂ * t⁻¹ = w⁻¹ * b₂ := by
    have h2 : (t * b₂ * t⁻¹)⁻¹ = b₂⁻¹ * w := by
      have : w = b₂ * (t * b₂ * t⁻¹)⁻¹ := hw1
      rw [this]; group
    calc t * b₂ * t⁻¹ = ((t * b₂ * t⁻¹)⁻¹)⁻¹ := by group
      _ = (b₂⁻¹ * w)⁻¹ := by rw [h2]
      _ = w⁻¹ * b₂ := by group
  have hkey : ∀ (P : Subgroup G) (b' w' : G), P ≤ E → Nat.card P = 9 → c ∈ P → b' ∈ P →
      b' ∉ Z → w' ∈ Z → t * b' * t⁻¹ = b' * w' → (∀ x ∈ P, t * x * t⁻¹ ∈ P) →
      ∀ p ∈ P, t * p * t⁻¹ * p⁻¹ ∈ Z := by
    intro P b' w' hPE hP hcP hbP hbZ hwZ' htb' htP p hp
    obtain ⟨k, z, hz, rfl⟩ := exists_zpow_mul_of_card_nine hc3 hEcomm hE3 hPE hP hcP hbP hbZ p hp
    have hbE' : b' ∈ E := hPE hbP
    have hZE : Z ≤ E := (Subgroup.zpowers_le.mpr hcP).trans hPE
    have hwE : w' ∈ E := hZE hwZ'
    have hcommbw : Commute b' w' := hEcomm b' hbE' w' hwE
    have hconj : t * b' ^ k * t⁻¹ = (b' * w') ^ k := by
      rw [← htb']
      have := map_zpow (MulAut.conj t) b' k
      simpa [MulAut.conj_apply] using this
    have hexp : (b' * w') ^ k = b' ^ k * w' ^ k := hcommbw.mul_zpow k
    have hm : w' ^ k * (t * z * t⁻¹) * z⁻¹ ∈ Z :=
      mul_mem (mul_mem (Subgroup.zpow_mem _ hwZ' k) (htZ z hz)) (inv_mem hz)
    have hbkE : b' ^ k ∈ E := Subgroup.zpow_mem _ hbE' k
    have hmE : w' ^ k * (t * z * t⁻¹) * z⁻¹ ∈ E := hZE hm
    have hcomm2 : b' ^ k * (w' ^ k * (t * z * t⁻¹) * z⁻¹) =
        (w' ^ k * (t * z * t⁻¹) * z⁻¹) * b' ^ k := hEcomm _ hbkE _ hmE
    have hid : t * (b' ^ k * z) * t⁻¹ * (b' ^ k * z)⁻¹ =
        b' ^ k * (w' ^ k * (t * z * t⁻¹) * z⁻¹) * (b' ^ k)⁻¹ := by
      calc t * (b' ^ k * z) * t⁻¹ * (b' ^ k * z)⁻¹
          = (t * b' ^ k * t⁻¹) * (t * z * t⁻¹) * z⁻¹ * (b' ^ k)⁻¹ := by group
        _ = (b' ^ k * w' ^ k) * (t * z * t⁻¹) * z⁻¹ * (b' ^ k)⁻¹ := by rw [hconj, hexp]
        _ = b' ^ k * (w' ^ k * (t * z * t⁻¹) * z⁻¹) * (b' ^ k)⁻¹ := by group
    rw [hid, hcomm2]
    simpa using hm
  have h₁ := hkey P₁ b₁ w hP₁E hP₁ hcP₁ hb₁P hb₁Z hwZ hwb₁ ht₁
  have hZE : Z ≤ E := (Subgroup.zpowers_le.mpr hcP₁).trans hP₁E
  have h₂ := hkey P₂ b₂ w⁻¹ hP₂E hP₂ hcP₂ hb₂P hb₂Z (inv_mem hwZ)
    (by rw [hwb₂]; exact hEcomm _ (hZE (inv_mem hwZ)) _ (hP₂E hb₂P)) ht₂
  intro x hx
  have hxmem : x ∈ ((P₁ ⊔ P₂ : Subgroup G) : Set G) := by rw [hE]; exact hx
  rw [hset] at hxmem
  obtain ⟨p₁, hp₁, p₂, hp₂, hxx⟩ := hxmem
  have hxx : p₁ * p₂ = x := hxx
  subst hxx
  have hp₁ : p₁ ∈ P₁ := hp₁
  have hp₂ : p₂ ∈ P₂ := hp₂
  have hp₁E : p₁ ∈ E := hP₁E hp₁
  have hp₂E : p₂ ∈ E := hP₂E hp₂
  have hcomm3 : (t * p₂ * t⁻¹ * p₂⁻¹) ∈ E := hZE (h₂ p₂ hp₂)
  have hcomm4 : p₁ * (t * p₂ * t⁻¹ * p₂⁻¹) = (t * p₂ * t⁻¹ * p₂⁻¹) * p₁ := hEcomm _ hp₁E _ hcomm3
  have hid : t * (p₁ * p₂) * t⁻¹ * (p₁ * p₂)⁻¹ =
      (t * p₁ * t⁻¹ * p₁⁻¹) * (p₁ * (t * p₂ * t⁻¹ * p₂⁻¹) * p₁⁻¹) := by group
  rw [hid, hcomm4]
  have h2' : (t * p₂ * t⁻¹ * p₂⁻¹) * p₁ * p₁⁻¹ = t * p₂ * t⁻¹ * p₂⁻¹ := by group
  rw [h2']
  exact mul_mem (h₁ p₁ hp₁) (h₂ p₂ hp₂)

theorem m12NormLComm_of_mixed (hmix : YCfgMixed) : M12NormLComm := by
  intro G _ _ A c L E F a b R Y hY _ t htE htb htL
  obtain ⟨hD, hSL2, -, hEle, hEe, hE27, hEC, hEL, -⟩ := hY.hCfg
  have hcL : c ∈ L := mem_of_isSLThreePiTwo slTwoCenter hD hSL2
  have hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) :=
    ResProof.isSLThreePi_of_isSLThreePiTwo hD hSL2
  have hty : Item131bProof.HeisType (L ⧸ aschbacherSolvableCore 3 L) := Or.inl hSL
  obtain ⟨hcE, hP1, hP2, hsup⟩ :=
    Item131bProof.e_facts hD hty hcL (hEle.trans inf_le_left) hEe hE27 hEC hEL
  obtain ⟨hb1, hb2⟩ := hmix G A c L E F a b R Y hY
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := hEe.2
  have hcC : c ∈ Sec4.thetaQuotCentralizer L :=
    Sec12.mem_thetaQuotCentralizer_of_central hcL hD.le_centralizer
  have hP₁E : E ⊓ Sec4.thetaQuotCentralizer L ≤ E := inf_le_left
  have hP₂E : E ⊓ L ≤ E := inf_le_left
  have hZ : (E ⊓ Sec4.thetaQuotCentralizer L) ⊓ (E ⊓ L) = Subgroup.zpowers c := by
    have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (E ⊓ Sec4.thetaQuotCentralizer L) (E ⊓ L)
      (fun x hx y hy => hEcomm x hx.1 y hy.1)).1
    rw [hsup, hE27, hP1, hP2] at hcard
    have h3 : Nat.card ((E ⊓ Sec4.thetaQuotCentralizer L) ⊓ (E ⊓ L) : Subgroup G) = 3 := by
      omega
    have hle : Subgroup.zpowers c ≤ (E ⊓ Sec4.thetaQuotCentralizer L) ⊓ (E ⊓ L) :=
      Subgroup.zpowers_le.mpr ⟨⟨hcE, hcC⟩, ⟨hcE, hcL⟩⟩
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [h3, Nat.card_zpowers, hD.orderOf_eq]
  exact conj_commutator_mem_of_mixed hD.orderOf_eq hEcomm hE3 hP₁E hP₂E hsup hP1 hP2
    ⟨hcE, hcC⟩ ⟨hcE, hcL⟩ hZ
    (fun x hx => ⟨(Subgroup.mem_normalizer_iff.mp htE x).mp hx.1,
      Sec12.conj_mem_thetaQuotCentralizer htL hx.2⟩)
    (fun x hx => ⟨(Subgroup.mem_normalizer_iff.mp htE x).mp hx.1,
      (Subgroup.mem_normalizer_iff.mp htL x).mp hx.2⟩)
    (hY.hbE) (fun h => hb1 h) (fun h => hb2 h) htb

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
