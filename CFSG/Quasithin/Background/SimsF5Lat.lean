module

public import CFSG.Quasithin.Background.SimsF5Defs
public import Certificates.Certificate7600

public section

namespace CFSG.Quasithin.SimsF5

open CFSG.Quasithin.SimsF5Lat CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

@[expose] def latT : Subgroup GL6 := Subgroup.closure {g | g ∈ f5TGens}

@[expose] def latA : Subgroup GL6 := Subgroup.closure {g | g ∈ f5GensA}

@[expose] def latB : Subgroup GL6 := Subgroup.closure {g | g ∈ f5GensB}

@[expose] def latM1 : Subgroup GL6 := Subgroup.closure {g | g ∈ f5GensM1}

@[expose] def latM2 : Subgroup GL6 := Subgroup.closure {g | g ∈ f5GensM2}

@[expose] def latM0 : Subgroup GL6 := Subgroup.closure {g | g ∈ f5GensM0}

@[expose] def latExtra : GL6 := f5XM0

theorem tGens_eq :
    f5LatCert.tGens = [eJ {0, 1}, eJ {0, 2}, eJ {0, 3}, eJ {0, 4}, f5P1, f5P2, fDot] := by
  have e1 : f5E01 = eJ {0, 1} := Units.ext (by decide)
  have e2 : f5E02 = eJ {0, 2} := Units.ext (by decide)
  have e3 : f5E03 = eJ {0, 3} := Units.ext (by decide)
  have e4 : f5E04 = eJ {0, 4} := Units.ext (by decide)
  have e5 : f5F = fDot := Units.ext (by decide)
  show f5TGens = _
  simp only [f5TGens, e1, e2, e3, e4, e5]

theorem f5P1_val : (f5P1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) =
    (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 6)).permMatrix (ZMod 3) := by
  decide

theorem f5P2_val : (f5P2 : Matrix (Fin 6) (Fin 6) (ZMod 3)) =
    (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 6)).permMatrix (ZMod 3) := by
  decide

theorem latExtra_val :
    ((latExtra : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) =
    !![0, 1, 1, -1, 1, 0;
      0, 1, 1, 1, -1, 0;
      1, 0, 0, 0, 0, 0;
      0, 1, -1, -1, -1, 0;
      0, 1, -1, 1, 1, 0;
      0, 0, 0, 0, 0, 1] := by
  decide

theorem latT_le_latM1 : latT ≤ latM1 :=
  Subgroup.closure_mono fun _ hg => List.mem_append_left _ hg

theorem latT_le_latM2 : latT ≤ latM2 :=
  Subgroup.closure_mono fun _ hg => List.mem_append_left _ hg

theorem latT_le_latM0 : latT ≤ latM0 :=
  Subgroup.closure_mono fun _ hg => List.mem_append_left _ hg

theorem lat_closure_tGens_cons_le {x : GL6} {L : Subgroup GL6} (hT : latT ≤ L) (hx : x ∈ L) :
    Subgroup.closure {g | g ∈ f5TGens ++ [x]} ≤ L := by
  rw [Subgroup.closure_le]
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact hT (Subgroup.subset_closure h)
  · rw [List.mem_singleton.mp h]
    exact hx

theorem latT_le_iff {L : Subgroup GL6} : latT ≤ L ↔ ∀ g ∈ f5TGens, g ∈ L :=
  ⟨fun h g hg => h (Subgroup.subset_closure hg),
    fun h => (Subgroup.closure_le L).mpr fun g hg => h g hg⟩

theorem latM0_le_of_mem {L : Subgroup GL6} (hT : latT ≤ L) (hx : latExtra ∈ L) : latM0 ≤ L :=
  lat_closure_tGens_cons_le hT hx

theorem lat_ne_of_card_ne {H K : Subgroup GL6} (h : Nat.card H ≠ Nat.card K) : H ≠ K := by
  rintro rfl
  exact h rfl

theorem card_latT : Nat.card latT = 128 := Certificates.certificate7600.1

theorem card_latA : Nat.card latA = 384 := Certificates.certificate7600.2.1

theorem card_latB : Nat.card latB = 384 := Certificates.certificate7600.2.2.1

theorem card_latM1 : Nat.card latM1 = 1152 := Certificates.certificate7600.2.2.2.1

theorem card_latM2 : Nat.card latM2 = 1920 := Certificates.certificate7600.2.2.2.2.1

theorem card_latM0 : Nat.card latM0 = 51840 := Certificates.certificate7600.2.2.2.2.2.1

theorem lat_overgroups (Y : Subgroup GL6) (hTY : latT ≤ Y) (hYM : Y ≤ latM0) :
    Y = latT ∨ Y = latA ∨ Y = latB ∨ Y = latM1 ∨ Y = latM2 ∨ Y = latM0 :=
  Certificates.certificate7600.2.2.2.2.2.2.1 Y hTY hYM

theorem latA_le_latM1 : latA ≤ latM1 :=
  lat_closure_tGens_cons_le latT_le_latM1
    Certificates.certificate7600.2.2.2.2.2.2.2.1

theorem latB_le_latM1 : latB ≤ latM1 :=
  lat_closure_tGens_cons_le latT_le_latM1
    Certificates.certificate7600.2.2.2.2.2.2.2.2.1

theorem latM1_le_latM0 : latM1 ≤ latM0 :=
  lat_closure_tGens_cons_le latT_le_latM0
    Certificates.certificate7600.2.2.2.2.2.2.2.2.2.2.1

theorem latM2_le_latM0 : latM2 ≤ latM0 :=
  lat_closure_tGens_cons_le latT_le_latM0
    Certificates.certificate7600.2.2.2.2.2.2.2.2.2.2.2.1

theorem latM1_ne_latM0 : latM1 ≠ latM0 :=
  lat_ne_of_card_ne (by rw [card_latM1, card_latM0]; norm_num)

theorem latM2_ne_latM0 : latM2 ≠ latM0 :=
  lat_ne_of_card_ne (by rw [card_latM2, card_latM0]; norm_num)

theorem eq_latM1_or_eq_latM0 {Y : Subgroup GL6} (h1 : latM1 ≤ Y) (h2 : Y ≤ latM0) :
    Y = latM1 ∨ Y = latM0 := by
  have hd := Subgroup.card_dvd_of_le h1
  rcases lat_overgroups Y (latT_le_latM1.trans h1) h2 with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [card_latM1, card_latT] at hd
    omega
  · rw [card_latM1, card_latA] at hd
    omega
  · rw [card_latM1, card_latB] at hd
    omega
  · exact Or.inl rfl
  · rw [card_latM1, card_latM2] at hd
    omega
  · exact Or.inr rfl

theorem eq_latM2_or_eq_latM0 {Y : Subgroup GL6} (h1 : latM2 ≤ Y) (h2 : Y ≤ latM0) :
    Y = latM2 ∨ Y = latM0 := by
  have hd := Subgroup.card_dvd_of_le h1
  rcases lat_overgroups Y (latT_le_latM2.trans h1) h2 with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [card_latM2, card_latT] at hd
    omega
  · rw [card_latM2, card_latA] at hd
    omega
  · rw [card_latM2, card_latB] at hd
    omega
  · rw [card_latM2, card_latM1] at hd
    omega
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem lat_maximal_iff (Q : Subgroup GL6) :
    (latT ≤ Q ∧ Q ≤ latM0 ∧ Q ≠ latM0 ∧ ∀ R : Subgroup GL6, Q < R → R ≤ latM0 → R = latM0) ↔
      (Q = latM1 ∨ Q = latM2) := by
  constructor
  · rintro ⟨hTQ, hQM, hne, hmax⟩
    rcases lat_overgroups Q hTQ hQM with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (hmax latM1 (lt_of_le_of_ne latT_le_latM1
        (lat_ne_of_card_ne (by rw [card_latT, card_latM1]; norm_num))) latM1_le_latM0)
        latM1_ne_latM0
    · exact absurd (hmax latM1 (lt_of_le_of_ne latA_le_latM1
        (lat_ne_of_card_ne (by rw [card_latA, card_latM1]; norm_num))) latM1_le_latM0)
        latM1_ne_latM0
    · exact absurd (hmax latM1 (lt_of_le_of_ne latB_le_latM1
        (lat_ne_of_card_ne (by rw [card_latB, card_latM1]; norm_num))) latM1_le_latM0)
        latM1_ne_latM0
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hne
  · rintro (rfl | rfl)
    · refine ⟨latT_le_latM1, latM1_le_latM0, latM1_ne_latM0, fun R hR hRM => ?_⟩
      rcases eq_latM1_or_eq_latM0 hR.le hRM with h | h
      · exact absurd h hR.ne'
      · exact h
    · refine ⟨latT_le_latM2, latM2_le_latM0, latM2_ne_latM0, fun R hR hRM => ?_⟩
      rcases eq_latM2_or_eq_latM0 hR.le hRM with h | h
      · exact absurd h hR.ne'
      · exact h

end CFSG.Quasithin.SimsF5
