module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Gen
public import CFSG.Timmesfeld.RankTwo.ModelG2
public import Certificates.Certificate113
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.Quasithin.Vol2.Ch11SecBFacts
public import CFSG.Quasithin.Vol2.Ch11SecCFacts
public import CFSG.Quasithin.Vol2.Ch11SecCFacts2
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.KGNatSL2
public import CFSG.Quasithin.Vol2.KGNatSL3Flag
public import CFSG.Sporadic.Schreier.J4SSylow

public section

namespace CFSG.Quasithin.B42G2Id

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.Ch11.G2Q8 Matrix
open CFSG.Timmesfeld.RankTwo (hexRoot hexRoot_injective)
open scoped commutatorElement

variable {F : Type} [Field F] [CharP F 2]

@[expose] noncomputable def zPos : Fin 6 → F → ↥(cayleyGroup F)
  | 0, c => g2X ![c, 0, 0]
  | 1, c => g2A (tv 0 2 (by decide) c)
  | 2, c => g2Y ![0, 0, c]
  | 3, c => g2A (tv 1 2 (by decide) c)
  | 4, c => g2X ![0, c, 0]
  | 5, c => g2A (tv 1 0 (by decide) c)

@[expose] noncomputable def zNeg : Fin 6 → F → ↥(cayleyGroup F)
  | 0, c => g2Y ![c, 0, 0]
  | 1, c => g2A (tv 2 0 (by decide) c)
  | 2, c => g2X ![0, 0, c]
  | 3, c => g2A (tv 2 1 (by decide) c)
  | 4, c => g2Y ![0, c, 0]
  | 5, c => g2A (tv 0 1 (by decide) c)

theorem g2Act_tv02 (t a b c d e f : F) :
    g2Act (g2A (tv 0 2 (by decide) t)) (q6 a b c d e f) = q6 (a + t * c) b c d e (f + t * d) := by
  rw [g2Act_tv]
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6]

theorem g2Act_tv12 (t a b c d e f : F) :
    g2Act (g2A (tv 1 2 (by decide) t)) (q6 a b c d e f) = q6 a (b + t * c) c d e (f + t * e) := by
  rw [g2Act_tv]
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6]

theorem g2Act_tv10 (t a b c d e f : F) :
    g2Act (g2A (tv 1 0 (by decide) t)) (q6 a b c d e f) = q6 a (b + t * a) c (d + t * e) e f := by
  rw [g2Act_tv]
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6]

theorem g2Act_tv20 (t a b c d e f : F) :
    g2Act (g2A (tv 2 0 (by decide) t)) (q6 a b c d e f) = q6 a b (c + t * a) (d + t * f) e f := by
  rw [g2Act_tv]
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6]

theorem g2Act_tv21 (t a b c d e f : F) :
    g2Act (g2A (tv 2 1 (by decide) t)) (q6 a b c d e f) = q6 a b (c + t * b) d (e + t * f) f := by
  rw [g2Act_tv]
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6]

theorem g2Act_tv01 (t a b c d e f : F) :
    g2Act (g2A (tv 0 1 (by decide) t)) (q6 a b c d e f) = q6 (a + t * b) b c d (e + t * d) f := by
  rw [g2Act_tv]
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6]

theorem g2Act_sl3P (a b c d e f : F) :
    g2Act (g2A (sl3P : SL3 F)) (q6 a b c d e f) = q6 b a c e d f := by
  rw [g2Act_g2A]
  simp [sl3P, adjugate_fin_three, CharTwo.neg_eq]

theorem g2Act_gW (a b c d e f : F) : g2Act (gW : ↥(cayleyGroup F)) (q6 a b c d e f) =
    q6 d f e a c b := by
  rw [gW, g2Act_mul_apply', g2Act_mul_apply', g2Act_x0q, g2Act_y0q, g2Act_x0q]
  apply q6_congr <;> ring_nf <;> reduce_mod_char!

local macro "zorn_q" : tactic => `(tactic| (
  refine cayley_ext_Q fun w => ?_
  rw [q6_eta w]
  simp only [g2Act_mul_apply', g2Act_sl3P, g2Act_gW, g2Act_x0q, g2Act_x1q, g2Act_x2q,
    g2Act_y0q, g2Act_y1q, g2Act_y2q, g2Act_tv02, g2Act_tv12, g2Act_tv10, g2Act_tv20,
    g2Act_tv21, g2Act_tv01, map_one, AddMonoid.End.coe_one, id_eq] <;>
  apply q6_congr <;> ring_nf <;> reduce_mod_char!))

theorem zPos_inv (i : Fin 6) (c : F) : (zPos i c)⁻¹ = zPos i c := by
  fin_cases i <;> simp only [zPos, g2X_inv, g2Y_inv, ← map_inv, tv_inv]

theorem zNeg_inv (i : Fin 6) (c : F) : (zNeg i c)⁻¹ = zNeg i c := by
  fin_cases i <;> simp only [zNeg, g2X_inv, g2Y_inv, ← map_inv, tv_inv]

theorem zPos_add (i : Fin 6) (c d : F) : zPos i (c + d) = zPos i c * zPos i d := by
  fin_cases i <;> simp only [zPos] <;> zorn_q

theorem zNeg_add (i : Fin 6) (c d : F) : zNeg i (c + d) = zNeg i c * zNeg i d := by
  fin_cases i <;> simp only [zNeg] <;> zorn_q

theorem zPos_comm02 (s t : F) : ⁅zPos 0 s, zPos 2 t⁆ = zPos 1 (s * t) := by
  rw [commutatorElement_def, zPos_inv, zPos_inv]
  simp only [zPos]
  zorn_q

theorem zPos_comm24 (s t : F) : ⁅zPos 2 s, zPos 4 t⁆ = zPos 3 (s * t) := by
  rw [commutatorElement_def, zPos_inv, zPos_inv]
  simp only [zPos]
  zorn_q

theorem zPos_comm15 (s t : F) : ⁅zPos 1 s, zPos 5 t⁆ = zPos 3 (s * t) := by
  rw [commutatorElement_def, zPos_inv, zPos_inv]
  simp only [zPos]
  zorn_q

theorem zPos_comm04 (s t : F) :
    ⁅zPos 0 s, zPos 4 t⁆ = zPos 1 (s ^ 2 * t) * zPos 3 (s * t ^ 2) := by
  rw [commutatorElement_def, zPos_inv, zPos_inv]
  simp only [zPos]
  zorn_q

theorem zPos_comm05 (s t : F) : ⁅zPos 0 s, zPos 5 t⁆ =
    zPos 1 (t * s ^ 3) * zPos 2 (t * s ^ 2) * zPos 3 (t ^ 2 * s ^ 3) * zPos 4 (t * s) := by
  rw [commutatorElement_def, zPos_inv, zPos_inv]
  simp only [zPos]
  zorn_q

theorem zPos_commute {i j : Fin 6}
    (hij : (i, j) ∈ ({(0, 1), (0, 3), (1, 2), (1, 3), (1, 4), (2, 3), (2, 5), (3, 4), (3, 5),
      (4, 5)} : Finset (Fin 6 × Fin 6))) (s t : F) : Commute (zPos i s) (zPos j t) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hij
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (simp only [Commute, SemiconjBy, zPos]; zorn_q)

theorem zPos_rels : ∀ r ∈ CFSG.Timmesfeld.GradedPresentation.rels
    (CFSG.Timmesfeld.RankTwo.g2Cm (K := F)),
    FreeGroup.lift (fun g : Σ _ : Fin 6, F => zPos g.1 g.2) r = 1 :=
  CFSG.Timmesfeld.RankTwo.rels_g2Cm_of (fun i c d => zPos_add i c d) zPos_comm02 zPos_comm24
    zPos_comm15 zPos_comm04 zPos_comm05 (zPos_commute (by decide)) (zPos_commute (by decide))
    (zPos_commute (by decide)) (zPos_commute (by decide)) (zPos_commute (by decide))
    (zPos_commute (by decide)) (zPos_commute (by decide)) (zPos_commute (by decide))
    (zPos_commute (by decide)) (zPos_commute (by decide))

@[expose] noncomputable def zW (F : Type) [Field F] [CharP F 2] : Fin 2 → ↥(cayleyGroup F)
  | 0 => g2A (sl3P : SL3 F)
  | 1 => (gW : ↥(cayleyGroup F))

theorem zW_mul_self (i : Fin 2) : zW F i * zW F i = 1 := by
  fin_cases i <;> simp only [zW] <;> zorn_q

theorem zW_inv (i : Fin 2) : (zW F i)⁻¹ = zW F i :=
  inv_eq_of_mul_eq_one_right (zW_mul_self i)

open Classical in
@[expose] noncomputable def zPsi (γ : Fin 2 → ℤ) (c : F) : ↥(cayleyGroup F) :=
  if h : ∃ i, hexRoot i = γ then zPos h.choose c
  else if h' : ∃ i, -hexRoot i = γ then zNeg h'.choose c else 1

theorem hexRoot_ne_neg (i j : Fin 6) :
    hexRoot i ≠ -hexRoot j := by
  have hpos : ∀ k : Fin 6, 0 ≤ hexRoot k 0 ∧
      0 ≤ hexRoot k 1 ∧
      0 < hexRoot k 0 + hexRoot k 1 := by
    intro k
    fin_cases k <;> decide
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Pi.neg_apply] at h0 h1
  have := hpos i
  have := hpos j
  omega

theorem zPsi_pos (j : Fin 6) (c : F) : zPsi (hexRoot j) c = zPos j c := by
  classical
  have h : ∃ i, hexRoot i = hexRoot j := ⟨j, rfl⟩
  rw [zPsi, dite_eq_left h, hexRoot_injective h.choose_spec]

theorem zPsi_neg (j : Fin 6) (c : F) :
    zPsi (-hexRoot j) c = zNeg j c := by
  classical
  have h1 : ¬ ∃ i, hexRoot i = -hexRoot j :=
    fun ⟨i, hi⟩ => hexRoot_ne_neg i j hi
  have h2 : ∃ i, -hexRoot i = -hexRoot j :=
    ⟨j, rfl⟩
  rw [zPsi, dite_eq_right h1, dite_eq_left h2,
    hexRoot_injective (neg_injective h2.choose_spec)]

abbrev g2Refl (i : Fin 2) (v : Fin 2 → ℤ) : Fin 2 → ℤ :=
  CFSG.LieType.RootSystem.reflection (CFSG.Blueprint.Chevalley.Tag.cartan .G2) i v

theorem zW_conj_zPos : ∀ (i : Fin 2) (j : Fin 6) (c : F),
    zW F i * zPos j c * (zW F i)⁻¹ = zPsi (g2Refl i (hexRoot j)) c
  | 0, 0, c => by
    rw [show g2Refl 0 (hexRoot 0) = hexRoot 4 by
      funext k; fin_cases k <;> decide, zPsi_pos, zW_inv]
    simp only [zW, zPos]; zorn_q
  | 0, 1, c => by
    rw [show g2Refl 0 (hexRoot 1) = hexRoot 3 by
      funext k; fin_cases k <;> decide, zPsi_pos, zW_inv]
    simp only [zW, zPos]; zorn_q
  | 0, 2, c => by
    rw [show g2Refl 0 (hexRoot 2) = hexRoot 2 by
      funext k; fin_cases k <;> decide, zPsi_pos, zW_inv]
    simp only [zW, zPos]; zorn_q
  | 0, 3, c => by
    rw [show g2Refl 0 (hexRoot 3) = hexRoot 1 by
      funext k; fin_cases k <;> decide, zPsi_pos, zW_inv]
    simp only [zW, zPos]; zorn_q
  | 0, 4, c => by
    rw [show g2Refl 0 (hexRoot 4) = hexRoot 0 by
      funext k; fin_cases k <;> decide, zPsi_pos, zW_inv]
    simp only [zW, zPos]; zorn_q
  | 0, 5, c => by
    rw [show g2Refl 0 (hexRoot 5) = -hexRoot 5 by
      funext k; fin_cases k <;> decide, zPsi_neg, zW_inv]
    simp only [zW, zPos, zNeg]; zorn_q
  | 1, 0, c => by
    rw [show g2Refl 1 (hexRoot 0) = -hexRoot 0 by
      funext k; fin_cases k <;> decide, zPsi_neg, zW_inv]
    simp only [zW, zPos, zNeg]; zorn_q
  | 1, 1, c => by
    rw [show g2Refl 1 (hexRoot 1) = hexRoot 5 by
      funext k; fin_cases k <;> decide, zPsi_pos, zW_inv]
    simp only [zW, zPos]; zorn_q
  | 1, 2, c => by
    rw [show g2Refl 1 (hexRoot 2) = hexRoot 4 by
      funext k; fin_cases k <;> decide, zPsi_pos, zW_inv]
    simp only [zW, zPos]; zorn_q
  | 1, 3, c => by
    rw [show g2Refl 1 (hexRoot 3) = hexRoot 3 by
      funext k; fin_cases k <;> decide, zPsi_pos, zW_inv]
    simp only [zW, zPos]; zorn_q
  | 1, 4, c => by
    rw [show g2Refl 1 (hexRoot 4) = hexRoot 2 by
      funext k; fin_cases k <;> decide, zPsi_pos, zW_inv]
    simp only [zW, zPos]; zorn_q
  | 1, 5, c => by
    rw [show g2Refl 1 (hexRoot 5) = hexRoot 1 by
      funext k; fin_cases k <;> decide, zPsi_pos, zW_inv]
    simp only [zW, zPos]; zorn_q

theorem zW_conj_zNeg : ∀ (i : Fin 2) (j : Fin 6) (c : F),
    zW F i * zNeg j c * (zW F i)⁻¹ = zPsi (-g2Refl i (hexRoot j)) c
  | 0, 0, c => by
    rw [show g2Refl 0 (hexRoot 0) = hexRoot 4 by
      funext k; fin_cases k <;> decide, zPsi_neg, zW_inv]
    simp only [zW, zNeg]; zorn_q
  | 0, 1, c => by
    rw [show g2Refl 0 (hexRoot 1) = hexRoot 3 by
      funext k; fin_cases k <;> decide, zPsi_neg, zW_inv]
    simp only [zW, zNeg]; zorn_q
  | 0, 2, c => by
    rw [show g2Refl 0 (hexRoot 2) = hexRoot 2 by
      funext k; fin_cases k <;> decide, zPsi_neg, zW_inv]
    simp only [zW, zNeg]; zorn_q
  | 0, 3, c => by
    rw [show g2Refl 0 (hexRoot 3) = hexRoot 1 by
      funext k; fin_cases k <;> decide, zPsi_neg, zW_inv]
    simp only [zW, zNeg]; zorn_q
  | 0, 4, c => by
    rw [show g2Refl 0 (hexRoot 4) = hexRoot 0 by
      funext k; fin_cases k <;> decide, zPsi_neg, zW_inv]
    simp only [zW, zNeg]; zorn_q
  | 0, 5, c => by
    rw [show g2Refl 0 (hexRoot 5) = -hexRoot 5 by
      funext k; fin_cases k <;> decide, neg_neg, zPsi_pos, zW_inv]
    simp only [zW, zPos, zNeg]; zorn_q
  | 1, 0, c => by
    rw [show g2Refl 1 (hexRoot 0) = -hexRoot 0 by
      funext k; fin_cases k <;> decide, neg_neg, zPsi_pos, zW_inv]
    simp only [zW, zPos, zNeg]; zorn_q
  | 1, 1, c => by
    rw [show g2Refl 1 (hexRoot 1) = hexRoot 5 by
      funext k; fin_cases k <;> decide, zPsi_neg, zW_inv]
    simp only [zW, zNeg]; zorn_q
  | 1, 2, c => by
    rw [show g2Refl 1 (hexRoot 2) = hexRoot 4 by
      funext k; fin_cases k <;> decide, zPsi_neg, zW_inv]
    simp only [zW, zNeg]; zorn_q
  | 1, 3, c => by
    rw [show g2Refl 1 (hexRoot 3) = hexRoot 3 by
      funext k; fin_cases k <;> decide, zPsi_neg, zW_inv]
    simp only [zW, zNeg]; zorn_q
  | 1, 4, c => by
    rw [show g2Refl 1 (hexRoot 4) = hexRoot 2 by
      funext k; fin_cases k <;> decide, zPsi_neg, zW_inv]
    simp only [zW, zNeg]; zorn_q
  | 1, 5, c => by
    rw [show g2Refl 1 (hexRoot 5) = hexRoot 1 by
      funext k; fin_cases k <;> decide, zPsi_neg, zW_inv]
    simp only [zW, zNeg]; zorn_q

theorem g2_root_cases {γ : Fin 2 → ℤ} (hγ : CFSG.Blueprint.Chevalley.IsRoot .G2 γ) :
    ∃ j, γ = hexRoot j ∨ γ = -hexRoot j := by
  obtain ⟨k, hk, rfl⟩ := CFSG.Blueprint.Chevalley.RootCertificate.exists_root_eq
    (CFSG.Blueprint.Chevalley.Tag.rootCertificate_check .G2) hγ
  have hk' : k < 12 := hk
  interval_cases k <;>
    first
    | (refine ⟨0, Or.inl ?_⟩; funext k; fin_cases k <;> decide)
    | (refine ⟨1, Or.inl ?_⟩; funext k; fin_cases k <;> decide)
    | (refine ⟨2, Or.inl ?_⟩; funext k; fin_cases k <;> decide)
    | (refine ⟨3, Or.inl ?_⟩; funext k; fin_cases k <;> decide)
    | (refine ⟨4, Or.inl ?_⟩; funext k; fin_cases k <;> decide)
    | (refine ⟨5, Or.inl ?_⟩; funext k; fin_cases k <;> decide)
    | (refine ⟨0, Or.inr ?_⟩; funext k; fin_cases k <;> decide)
    | (refine ⟨1, Or.inr ?_⟩; funext k; fin_cases k <;> decide)
    | (refine ⟨2, Or.inr ?_⟩; funext k; fin_cases k <;> decide)
    | (refine ⟨3, Or.inr ?_⟩; funext k; fin_cases k <;> decide)
    | (refine ⟨4, Or.inr ?_⟩; funext k; fin_cases k <;> decide)
    | (refine ⟨5, Or.inr ?_⟩; funext k; fin_cases k <;> decide)

theorem zW_conj_zPsi (i : Fin 2) {γ : Fin 2 → ℤ} (hγ : CFSG.Blueprint.Chevalley.IsRoot .G2 γ)
    (c : F) : zW F i * zPsi γ c * (zW F i)⁻¹ = zPsi (g2Refl i γ) c := by
  obtain ⟨j, rfl | rfl⟩ := g2_root_cases hγ
  · rw [zPsi_pos]
    exact zW_conj_zPos i j c
  · rw [zPsi_neg, show g2Refl i (-hexRoot j) =
      -g2Refl i (hexRoot j) from
      map_neg (CFSG.LieType.RootSystem.reflection (CFSG.Blueprint.Chevalley.Tag.cartan .G2) i)
        (hexRoot j)]
    exact zW_conj_zNeg i j c

end CFSG.Quasithin.B42G2Id
