module

public import CFSG.Quasithin.Background.ShultG53Model
public import CFSG.Permutation.FinPackEven6
public import CFSG.Permutation.FinPackF2

public section

namespace CFSG.Quasithin.ShultG53.Pack

open CFSG.Permutation.FinPack CFSG.CharacterTheory.SteinbergBY.AlternatingSix Equiv Matrix

@[expose] def heartT : ℕ := 5278959

@[expose] def hd (c i : ℕ) : ℕ := rd heartT (rd c i)

@[expose] def hK (c x : ℕ) : ℕ :=
  linK (Nat.xor (hd c 0) (hd c 1)) (Nat.xor (hd c 1) (hd c 2)) (Nat.xor (hd c 2) (hd c 3))
    (Nat.xor (hd c 3) (hd c 4)) x

theorem vc_heartCoord : ∀ l : Fin 6, vc (fun i => heartCoord i l) = rd heartT l := by
  decide +kernel

theorem mulVec_eq (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (v : Fin 4 → ZMod 2) :
    M *ᵥ v = v 0 • (fun i => M i 0) + v 1 • (fun i => M i 1) + v 2 • (fun i => M i 2) +
      v 3 • (fun i => M i 3) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem vc_heart (f : Fin 6 → Fin 6) (c : ℕ) (hc : ∀ i : Fin 6, rd c i = f i)
    (v : Fin 4 → ZMod 2) : vc (heartMatrixOf f *ᵥ v) = hK c (vc v) := by
  have hcol : ∀ a b : Fin 6, vc ((fun i => heartCoord i a) + fun i => heartCoord i b) =
      Nat.xor (rd heartT a) (rd heartT b) := fun a b => by
    rw [vc_add, vc_heartCoord, vc_heartCoord]
  have h : ∀ i : Fin 6, rd heartT (f i) = hd c i := fun i => by rw [hd, hc]
  rw [mulVec_eq, vc_lin, hK]
  have e0 : (fun i => heartMatrixOf f i 0) =
      (fun i => heartCoord i (f 0)) + fun i => heartCoord i (f 1) := rfl
  have e1 : (fun i => heartMatrixOf f i 1) =
      (fun i => heartCoord i (f 1)) + fun i => heartCoord i (f 2) := rfl
  have e2 : (fun i => heartMatrixOf f i 2) =
      (fun i => heartCoord i (f 2)) + fun i => heartCoord i (f 3) := rfl
  have e3 : (fun i => heartMatrixOf f i 3) =
      (fun i => heartCoord i (f 3)) + fun i => heartCoord i (f 4) := rfl
  rw [e0, e1, e2, e3, hcol, hcol, hcol, hcol, h 0, h 1, h 2, h 3, h 4]
  rfl

@[expose] def partnerT : ℕ :=
  44791721718786784299229942976193593337680015635989565633015849440076024110220438958657464868541662743060169372857750091622102664975513545596242697461957430381757357056007974966601673474332004971160258917655311098625

@[expose] def pK (j a x : ℕ) : ℕ := rd partnerT (Nat.add (Nat.add (Nat.mul 30 j) (Nat.mul 6 a)) x)

theorem pK_eq : ∀ (j : Fin 6) (a : Fin 5) (x : Fin 6), pK j a x = partner j a x := by
  decide +kernel

@[expose] def l5 : List ℕ := [0, 1, 2, 3, 4]

@[expose] def l6 : List ℕ := [0, 1, 2, 3, 4, 5]

theorem l5_eq : l5 = List.range 5 := by decide

theorem l6_eq : l6 = List.range 6 := by decide

@[expose] noncomputable def mapsK (c j i : ℕ) : Bool :=
  allK (fun a => anyK (fun b => allK (fun x => Nat.beq (rd c (pK j a x)) (pK i b (rd c x))) l6)
    l5) l5

theorem forall_fin {n : ℕ} {l : List ℕ} (hl : l = List.range n) {P : ℕ → Prop} :
    (∀ a : Fin n, P a) ↔ ∀ a ∈ l, P a := by
  rw [hl]
  exact ⟨fun h a ha => h ⟨a, List.mem_range.1 ha⟩, fun h a => h a (List.mem_range.2 a.isLt)⟩

theorem exists_fin {n : ℕ} {l : List ℕ} (hl : l = List.range n) {P : ℕ → Prop} :
    (∃ a : Fin n, P a) ↔ ∃ a ∈ l, P a := by
  rw [hl]
  exact ⟨fun ⟨a, h⟩ => ⟨a, List.mem_range.2 a.isLt, h⟩,
    fun ⟨a, ha, h⟩ => ⟨⟨a, List.mem_range.1 ha⟩, h⟩⟩

theorem mapsK_iff (σ : Perm (Fin 6)) (j i : Fin 6) :
    MapsTotal σ j i ↔ mapsK (enc σ) j i = true := by
  have hr : ∀ y : Fin 6, rd (enc σ) y = σ y := rd_enc (by norm_num) σ
  rw [MapsTotal, mapsK, allK_iff]
  refine Iff.trans ?_ (forall_fin l5_eq)
  refine forall_congr' fun a => ?_
  rw [anyK_iff]
  refine Iff.trans ?_ (exists_fin l5_eq)
  refine exists_congr fun b => ?_
  rw [allK_iff]
  refine Iff.trans ?_ (forall_fin l6_eq)
  refine forall_congr' fun x => ?_
  rw [pK_eq, hr, hr, pK_eq, Nat.beq_eq, Fin.val_inj]

@[expose] noncomputable def find6 (f : ℕ → Bool) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) 5 4 (f 4)) 3 (f 3)) 2 (f 2)) 1 (f 1)) 0 (f 0)

theorem find6_lt (f : ℕ → Bool) : find6 f < 6 := by
  rw [find6]
  cases f 0 <;> cases f 1 <;> cases f 2 <;> cases f 3 <;> cases f 4 <;> decide

theorem find6_spec {f : ℕ → Bool} {i : ℕ} (hi : i < 6) (hf : f i = true) :
    f (find6 f) = true := by
  have h5 : f 0 = false → f 1 = false → f 2 = false → f 3 = false → f 4 = false →
      f 5 = true := by
    intro h0 h1 h2 h3 h4
    interval_cases i <;> simp_all
  rw [find6]
  cases h0 : f 0 <;> cases h1 : f 1 <;> cases h2 : f 2 <;> cases h3 : f 3 <;> cases h4 : f 4 <;>
    simp_all

@[expose] noncomputable def tK (c j : ℕ) : ℕ := find6 (fun i => mapsK c j i)

@[expose] noncomputable def totK (c : ℕ) : ℕ := encF (fun j => tK c j) 6

theorem tK_eq (σ : Perm (Fin 6)) (j : Fin 6) : tK (enc σ) j = totalIdx σ j := by
  obtain ⟨i, hi⟩ := exists_mapsTotal σ j
  have h1 := find6_spec (f := fun i => mapsK (enc σ) j i) i.isLt ((mapsK_iff σ j i).1 hi)
  have hm : MapsTotal σ j ⟨tK (enc σ) j, find6_lt _⟩ := (mapsK_iff σ j _).2 h1
  rw [(mapsTotal_totalIdx σ j).unique hm]

theorem rd_totK (σ : Perm (Fin 6)) (j : Fin 6) : rd (totK (enc σ)) j = totalIdx σ j := by
  rw [totK, rd_encF (a := fun i => tK (enc σ) i) (fun i _ => lt_trans (find6_lt _) (by norm_num))
    j.isLt, tK_eq]

theorem vc_Rm0 (σ : Perm (Fin 6)) (v : V4) : vc (Rm 0 σ *ᵥ v) = hK (enc σ) (vc v) := by
  rw [Rm, if_pos rfl]
  exact vc_heart σ (enc σ) (rd_enc (by norm_num) σ) v

theorem vc_Rm1 (σ : Perm (Fin 6)) (v : V4) : vc (Rm 1 σ *ᵥ v) = hK (totK (enc σ)) (vc v) := by
  rw [Rm, if_neg (by decide)]
  exact vc_heart (totalIdx σ) (totK (enc σ)) (rd_totK σ) v

end CFSG.Quasithin.ShultG53.Pack
