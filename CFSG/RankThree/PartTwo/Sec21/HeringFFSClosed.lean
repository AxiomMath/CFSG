module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFSStruct
public import CFSG.RankThree.PartTwo.Sec21.HeringFFSDec
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3FusionLines
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoThreeA6Cyclic
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38AbsB
public import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIU3EvenTools
public import CFSG.RankThree.PartTwo.Sec8.Item82ProofPGU
public import CFSG.Quasithin.Background.A1cA131Three

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.Open (IsElemAbelian)

theorem ffs_exists_mul_mem_normalizer {G : Type} [Group G] [Finite G] {a w : G}
    {A B C : Subgroup G} (hC : C = Subgroup.centralizer ({a} : Set G)) (P : Sylow 3 C)
    (hPB : (P : Subgroup C).map C.subtype = B) (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (haA : a ∈ A) (hAB : A ≤ B) (hw : w ∈ Subgroup.normalizer (A : Set G)) :
    ∃ c ∈ C, ∀ b ∈ B, w * c * b * (w * c)⁻¹ ∈ B := by
  have haw : w * a * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hw a).mp haA
  have hawB : w * a * w⁻¹ ∈ B := hAB haw
  set B' : Subgroup G := B.map (MulAut.conj w⁻¹).toMonoidHom with hB'
  have hB'C : B' ≤ C := by
    rintro _ ⟨b, hb, rfl⟩
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    have h1 : b * (w * a * w⁻¹) = (w * a * w⁻¹) * b := hBab b hb _ hawB
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc w⁻¹ * b * w * a = w⁻¹ * (b * (w * a * w⁻¹)) * w := by group
      _ = w⁻¹ * ((w * a * w⁻¹) * b) * w := by rw [h1]
      _ = a * (w⁻¹ * b * w) := by group
  have hB'card : Nat.card B' = Nat.card (P : Subgroup C) := by
    rw [hB', Subgroup.card_map_of_injective (MulAut.conj w⁻¹).injective, ← hPB,
      Subgroup.card_map_of_injective C.subtype_injective]
  obtain ⟨c, hcC, hc⟩ := ffs_exists_conj_mem_of_card_eq P hB'C hB'card
  refine ⟨c, hcC, fun b hb => ?_⟩
  obtain ⟨b₀, hb₀, hb₀eq⟩ := hc b (hPB ▸ hb)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hb₀eq
  have : w * c * b * (w * c)⁻¹ = b₀ := by
    calc w * c * b * (w * c)⁻¹ = w * (c * b * c⁻¹) * w⁻¹ := by group
      _ = w * (w⁻¹ * b₀ * w) * w⁻¹ := by rw [hb₀eq]
      _ = b₀ := by group
  rw [this]
  exact hb₀

theorem ffs_main {G : Type} [Group G] [Finite G] {a : G} {A X : Subgroup G}
    (hA : IsElemAbelian 3 A) (hAmax : ∀ B : Subgroup G, IsElemAbelian 3 B → A ≤ B → B = A)
    (haA : a ∈ A) (ha1 : a ≠ 1) (hXC : X ≤ Subgroup.centralizer ({a} : Set G))
    (hCN : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥X))
    (hE : ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian 3 E ∧ Nat.card E = 9)
    (hQ : ∀ R : Subgroup (↥X ⧸ Subgroup.center ↥X), IsPGroup 3 R → Nat.card R ≤ 9)
    (hI : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ k : ℕ, g ^ (3 ^ k) = 1 →
      ∃ x ∈ X, x⁻¹ * g ∈ Subgroup.centralizer (X : Set G))
    (hcyc : ∀ P : Sylow 3 ↥(Subgroup.centralizer (X : Set G)),
      IsCyclic ↥(P : Subgroup ↥(Subgroup.centralizer (X : Set G))))
    (hW : ¬ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G)) :
    (∃ P : Sylow 3 ↥(Subgroup.centralizer ({a} : Set G)),
      (P : Subgroup ↥(Subgroup.centralizer ({a} : Set G))).map
        (Subgroup.centralizer ({a} : Set G)).subtype = A) ∧ Nat.card A ≤ 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAC : A ≤ C := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAab a haA x hx).symm
  have ha3 : a ^ 3 = 1 := hA.2 a haA
  have hAp : IsPGroup 3 A := hA.isPGroup
  obtain ⟨P, hAP⟩ := (hAp.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨B, hPB⟩ : ∃ B : Subgroup G, (P : Subgroup C).map C.subtype = B := ⟨_, rfl⟩
  have hAB : A ≤ B := by
    intro x hx
    rw [← hPB]
    exact ⟨⟨x, hAC hx⟩, hAP (show (⟨x, hAC hx⟩ : ↥C) ∈ A.comap C.subtype from hx), rfl⟩
  have hBC : B ≤ C := hPB ▸ Subgroup.map_subtype_le _
  have hB3 : IsPGroup 3 B := hPB ▸ P.isPGroup'.map C.subtype
  have hBN : B ≤ Subgroup.normalizer (X : Set G) := hBC.trans hCN
  have hI' : ∀ b ∈ B, ∃ x ∈ X, x⁻¹ * b ∈ Subgroup.centralizer (X : Set G) := by
    intro b hb
    obtain ⟨k, hk⟩ := hB3 ⟨b, hb⟩
    exact hI b (hBN hb) k (by simpa using congrArg Subtype.val hk)
  obtain ⟨hTel, hT9, hdec⟩ := ffs_decomp hXC hCN P hPB hZ hE hQ hI'
  set T : Subgroup G := B ⊓ X with hT
  set S : Subgroup G := B ⊓ Subgroup.centralizer (X : Set G) with hS
  have hTS : ∀ t ∈ T, ∀ s ∈ S, t * s = s * t := fun t ht s hs =>
    Subgroup.mem_centralizer_iff.mp hs.2 t ht.2
  have hS3 : IsPGroup 3 S := hB3.to_inf_left
  have hScyc : IsCyclic S :=
    CFSG.RankThree.PartTwo.Sec8.Item82Proof.isCyclic_of_le_of_forall_sylow hcyc hS3 inf_le_right
  have haS : a ∈ S := ⟨hAB haA, Subgroup.mem_centralizer_iff.mpr fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.mp (hXC hh)⟩
  have hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := ffs_comm_of_decomp hTel hScyc hTS hdec
  by_cases hcase : ∀ s ∈ S, s ^ 3 = 1
  ·
    have hBexp : ∀ b ∈ B, b ^ 3 = 1 := ffs_pow_three_eq_one_of_decomp hTel hTS hdec hcase
    have hBel : IsElemAbelian 3 B := ⟨⟨⟨fun x y => Subtype.ext (hBab x x.2 y y.2)⟩⟩, hBexp⟩
    have hBA : B = A := hAmax B hBel hAB
    refine ⟨⟨P, hPB.trans hBA⟩, ?_⟩
    have hSle : Nat.card S ≤ 3 := by
      haveI := hScyc
      have h := CFSG.RankThree.PartTwo.Sec4.Item434U38.card_le_three_of_pow (G' := ↥S) ⊤
        (fun r _ => Subtype.ext (hcase r r.2))
      rwa [Subgroup.card_top] at h
    have hBle : Nat.card B ≤ Nat.card T * Nat.card S :=
      CFSG.Quasithin.A1c.card_le_mul_of_forall_mul (inf_le_left : T ≤ B) (inf_le_left : S ≤ B)
        hdec
    rw [← hBA]
    calc Nat.card B ≤ Nat.card T * Nat.card S := hBle
      _ ≤ 9 * 3 := Nat.mul_le_mul hT9.le hSle
      _ = 27 := by norm_num
  ·
    exfalso
    obtain ⟨s, hsS, hs3⟩ : ∃ s ∈ S, s ^ 3 ≠ 1 := by
      by_contra hne
      exact hcase fun s hs => by_contra fun h => hne ⟨s, hs, h⟩
    have h9 : 9 ≤ Nat.card S := by
      obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hS3 ⟨s, hsS⟩
      have hs_ord : orderOf s = 3 ^ j := by rwa [Subgroup.orderOf_mk] at hj
      have hj2 : 2 ≤ j := by
        by_contra hlt
        have hlt := not_le.mp hlt
        apply hs3
        have : orderOf s ∣ 3 := by
          rw [hs_ord]
          interval_cases j <;> norm_num
        exact orderOf_dvd_iff_pow_eq_one.mp this
      have hdvd : 3 ^ j ∣ Nat.card S := hs_ord ▸ Subgroup.orderOf_dvd_natCard S hsS
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
        _ ≤ Nat.card S := Nat.le_of_dvd Nat.card_pos hdvd
    obtain ⟨y, hyS, hy3⟩ := CFSG.AGLEmbedding.exists_cube_eq_of_isCyclic hScyc hS3 h9 haS ha3
    have key : ∀ w ∈ Subgroup.normalizer (A : Set G), w * a * w⁻¹ ∈ Subgroup.zpowers a := by
      intro w hw
      obtain ⟨c, hcC, hc⟩ := ffs_exists_mul_mem_normalizer hC P hPB hBab haA hAB hw
      have hca : c * a = a * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
      have hna : w * c * a * (w * c)⁻¹ = w * a * w⁻¹ := by
        calc w * c * a * (w * c)⁻¹ = w * (c * a * c⁻¹) * w⁻¹ := by group
          _ = w * a * w⁻¹ := by rw [hca]; group
      have haB : a ∈ B := hAB haA
      have hyB : y ∈ B := hyS.1
      have hnaB : w * c * a * (w * c)⁻¹ ∈ B := hc a haB
      have hnyB : w * c * y * (w * c)⁻¹ ∈ B := hc y hyB
      obtain ⟨s', hs'S, hs'⟩ := ffs_pow_three_of_decomp hTel hTS hdec _ hnyB
      have hcube : (w * c * y * (w * c)⁻¹) ^ 3 = w * c * a * (w * c)⁻¹ := by
        rw [conj_pow, hy3]
      have hzS : w * c * a * (w * c)⁻¹ ∈ S := by
        rw [← hcube, hs']
        exact S.pow_mem hs'S 3
      have hz3 : (w * c * a * (w * c)⁻¹) ^ 3 = 1 := by
        rw [conj_pow, ha3]
        group
      have := CFSG.LocalAnalysis.RankThreeTheoremC.mem_zpowers_of_isCyclic_of_pow_three hScyc
        haS hzS ha1 ha3 hz3
      rwa [hna] at this
    apply hW
    intro w hw
    exact CFSG.RankThree.PartTwo.Sec18.mem_normalizer_zpowers_of_conj_mem189 (key w hw)
      (by simpa using key w⁻¹ (Subgroup.inv_mem _ hw))

end CFSG.RankThree.PartTwo.Sec21
