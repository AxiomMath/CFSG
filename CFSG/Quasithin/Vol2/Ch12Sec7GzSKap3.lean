module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzSKap2
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSKap

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277Struct
open scoped IsMulCommutative

theorem app_spec (G0 : List B6) {i c : Nat} (hi : i < G0.length) (hc : c < 64) :
    (mkTab G0).appA.getD (i * 64 + c) 0 = (G0.getD i B6.id).app c := by
  have h : i * 64 + c < G0.length * 64 := by omega
  have h1 : (i * 64 + c) / 64 = i := by omega
  have h2 : (i * 64 + c) % 64 = c := by omega
  simp [mkTab, h, h1, h2]

theorem comp_spec (G0 : List B6) {i j : Nat} (hi : i < G0.length) (hj : j < G0.length) :
    (mkTab G0).compA.getD (i * G0.length + j) 0 =
      G0.idxOf ((G0.getD i B6.id).comp (G0.getD j B6.id)) := by
  have h : i * G0.length + j < G0.length * G0.length := by
    have : i * G0.length + j < (i + 1) * G0.length := by rw [Nat.add_mul, Nat.one_mul]; omega
    calc i * G0.length + j < (i + 1) * G0.length := this
      _ ≤ G0.length * G0.length := Nat.mul_le_mul_right _ hi
  have h1 : (i * G0.length + j) / G0.length = i := by
    have hpos : 0 < G0.length := by omega
    rw [Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hj]; simp
  have h2 : (i * G0.length + j) % G0.length = j := by
    rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hj
  simp [mkTab, h, h1, h2]

theorem mulN_mk (G0 : List B6) {i j c c' : Nat} (hi : i < G0.length) (hj : j < G0.length)
    (hc : c < 64) (hc' : c' < 64) :
    mulN (mkTab G0) (i * 64 + c) (j * 64 + c') =
      G0.idxOf ((G0.getD i B6.id).comp (G0.getD j B6.id)) * 64 +
        (c ^^^ (G0.getD i B6.id).app c') := by
  have h1 : (i * 64 + c) / 64 = i := by omega
  have h2 : (i * 64 + c) % 64 = c := by omega
  have h3 : (j * 64 + c') / 64 = j := by omega
  have h4 : (j * 64 + c') % 64 = c' := by omega
  unfold mulN
  rw [h1, h2, h3, h4]
  have hnb : (mkTab G0).nb = G0.length := rfl
  rw [hnb, comp_spec G0 hi hj, app_spec G0 hi hc']


section KapDef

variable {G : Type} [Group G] [Finite G] {V M M₀ : Subgroup G} [IsMulCommutative ↥V]

open scoped Classical in
@[expose] noncomputable def kap (T : KTab) (C : Coding ↥V) (S : SplitHyp V M M₀) (m : G) : Nat :=
  T.G0.idxOf (bpart C S m) * 64 + cpart C S m

theorem cpart_lt (C : Coding ↥V) (S : SplitHyp V M M₀) (m : G) : cpart C S m < 64 := by
  unfold cpart
  split_ifs with h
  · exact C.cd_lt _
  · norm_num

theorem mem_stabL {Γ : List B6} {c₀ : Nat} {B : B6} :
    B ∈ stabL Γ c₀ ↔ B ∈ Γ ∧ B.app c₀ = c₀ := by
  unfold stabL
  rw [List.mem_filter]
  simp

theorem getD_idxOf {l : List B6} {B : B6} (hB : B ∈ l) : l.getD (l.idxOf B) B6.id = B := by
  have hlt : l.idxOf B < l.length := List.idxOf_lt_length_iff.2 hB
  rw [List.getD_eq_getElem _ _ hlt]
  exact List.getElem_idxOf hlt

theorem idxOf_getD {l : List B6} (hnd : l.Nodup) {i : Nat} (hi : i < l.length) :
    l.idxOf (l.getD i B6.id) = i := by
  rw [List.getD_eq_getElem _ _ hi]
  exact hnd.idxOf_getElem i hi

theorem bpart_mem_stabL (S : SplitHyp V M M₀) (C : Coding ↥V) {Γ : List B6} {c₀ : Nat} {z : G}
    (hΓ1 : ∀ a ∈ autOn M V, C.cB a ∈ Γ) (hz : z ∈ V) (hzc : C.cd ⟨z, hz⟩ = c₀) {m : G}
    (hm : m ∈ M ⊓ Subgroup.centralizer ({z} : Set G)) : bpart C S m ∈ stabL Γ c₀ := by
  have hmM : m ∈ M := (Subgroup.mem_inf.1 hm).1
  have hmz : m * z = z * m := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hm).2
  rw [mem_stabL, bpart_of_mem C S hmM]
  refine ⟨hΓ1 _ ((A4.mem_autOn_iff S.hMV).2 ⟨⟨m, hmM⟩, rfl⟩), ?_⟩
  have h1 := cd_conj C ⟨m, S.hMV hmM⟩ ⟨z, hz⟩
  have h2 : (conjAct V ⟨m, S.hMV hmM⟩ ⟨z, hz⟩ : ↥V) = ⟨z, hz⟩ := by
    apply Subtype.ext
    rw [conjAct_val]
    calc m * z * m⁻¹ = z * m * m⁻¹ := by rw [hmz]
      _ = z := by group
  rw [h2, hzc] at h1
  exact h1.symm

theorem kCod_of_split (S : SplitHyp V M M₀) (C : Coding ↥V) {Γ : List B6} {c₀ : Nat} {z : G}
    (hΓ1 : ∀ a ∈ autOn M V, C.cB a ∈ Γ) (hΓ2 : ∀ B ∈ Γ, ∃ a ∈ autOn M V, C.cB a = B)
    (hz : z ∈ V) (hzc : C.cd ⟨z, hz⟩ = c₀) (hnd : (stabL Γ c₀).Nodup) :
    KCod (M ⊓ Subgroup.centralizer ({z} : Set G)) (mkTab (stabL Γ c₀))
      (kap (mkTab (stabL Γ c₀)) C S) := by
  classical
  set G0 := stabL Γ c₀ with hG0
  set K : Subgroup G := M ⊓ Subgroup.centralizer ({z} : Set G) with hK
  have hTG0 : (mkTab G0).G0 = G0 := rfl
  have hbG0 : ∀ m ∈ K, bpart C S m ∈ G0 := fun m hm => bpart_mem_stabL S C hΓ1 hz hzc hm
  have hlt : ∀ m ∈ K, G0.idxOf (bpart C S m) < G0.length := fun m hm =>
    List.idxOf_lt_length_iff.2 (hbG0 m hm)
  have hget : ∀ m ∈ K, G0.getD (G0.idxOf (bpart C S m)) B6.id = bpart C S m := fun m hm =>
    getD_idxOf (hbG0 m hm)
  have hmulK : ∀ x ∈ K, ∀ y ∈ K, x * y ∈ K := fun x hx y hy => K.mul_mem hx hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx y hy
    have hxM : x ∈ M := (Subgroup.mem_inf.1 hx).1
    have hyM : y ∈ M := (Subgroup.mem_inf.1 hy).1
    unfold kap
    rw [hTG0]
    have := mulN_mk G0 (hlt x hx) (hlt y hy) (cpart_lt C S x) (cpart_lt C S y)
    rw [this, hget x hx, hget y hy, bpart_mul C S hxM hyM, cpart_mul C S hxM hyM]
  ·
    intro x hx y hy hxy
    have hxM : x ∈ M := (Subgroup.mem_inf.1 hx).1
    have hyM : y ∈ M := (Subgroup.mem_inf.1 hy).1
    unfold kap at hxy
    rw [hTG0] at hxy
    have hcx := cpart_lt C S x
    have hcy := cpart_lt C S y
    have hi : G0.idxOf (bpart C S x) = G0.idxOf (bpart C S y) := by omega
    have hc : cpart C S x = cpart C S y := by omega
    have hb : bpart C S x = bpart C S y := by
      rw [← hget x hx, ← hget y hy, hi]
    exact pair_inj C S hxM hyM hb hc
  ·
    intro x hx
    unfold kap klist
    rw [hTG0, List.mem_range]
    have := hlt x hx
    have := cpart_lt C S x
    show _ < G0.length * 64
    omega
  ·
    intro n hn
    unfold klist at hn
    rw [List.mem_range] at hn
    change n < G0.length * 64 at hn
    set i := n / 64 with hi
    set c := n % 64 with hc
    have hilt : i < G0.length := by omega
    have hclt : c < 64 := by omega
    have hn' : n = i * 64 + c := by omega
    have hBmem : G0.getD i B6.id ∈ G0 := by
      rw [List.getD_eq_getElem _ _ hilt]; exact List.getElem_mem hilt
    obtain ⟨hBΓ, hBfix⟩ := mem_stabL.1 hBmem
    obtain ⟨a, ha, hBa⟩ := hΓ2 _ hBΓ
    obtain ⟨⟨m₁, hm₁M⟩, hm₁a⟩ := (A4.mem_autOn_iff S.hMV).1 ha
    obtain ⟨h₁, hh₁, e₁⟩ := vOf_spec S hm₁M
    have hv₁ : vOf S m₁ ∈ V := vOf_mem S hm₁M
    have hbh : cj C ⟨h₁, S.hMV (S.hM0 hh₁)⟩ = G0.getD i B6.id := by
      have := bpart_decomp C S hv₁ hh₁ e₁
      rw [bpart_of_mem C S hm₁M] at this
      have e2 : cj C ⟨m₁, S.hMV hm₁M⟩ = C.cB a := by rw [← hm₁a]; rfl
      rw [← this, e2, hBa]
    set d : ↥V := C.dc c with hd
    set m : G := (d : G) * h₁ with hm
    have hmM : m ∈ M := M.mul_mem (S.hVM d.2) (S.hM0 hh₁)
    have hh₁z : h₁ * z * h₁⁻¹ = z := by
      have h1 := cd_conj C ⟨h₁, S.hMV (S.hM0 hh₁)⟩ ⟨z, hz⟩
      rw [hbh, hzc] at h1
      have hfix : (G0.getD i B6.id).app c₀ = c₀ := hBfix
      rw [hfix] at h1
      have h2 : conjAct V ⟨h₁, S.hMV (S.hM0 hh₁)⟩ ⟨z, hz⟩ = ⟨z, hz⟩ := by
        apply C.cd_injective
        rw [h1, hzc]
      have := congrArg Subtype.val h2
      rw [conjAct_val] at this
      exact this
    have hmz : m ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm : (d : G) * z = z * (d : G) :=
        congrArg Subtype.val (IsMulCommutative.is_comm.comm d ⟨z, hz⟩)
      calc m * z = (d : G) * (h₁ * z * h₁⁻¹) * h₁ := by rw [hm]; group
        _ = (d : G) * z * h₁ := by rw [hh₁z]
        _ = z * (d : G) * h₁ := by rw [hcomm]
        _ = z * m := by rw [hm]; group
    have hmK : m ∈ K := Subgroup.mem_inf.2 ⟨hmM, hmz⟩
    refine ⟨m, hmK, ?_⟩
    unfold kap
    rw [hTG0, bpart_decomp C S d.2 hh₁ hm, hbh, idxOf_getD hnd hilt, hn']
    congr 1
    have hvm : vOf S m = (d : G) := vOf_mul_of S d.2 hh₁
    unfold cpart
    have hvV : vOf S m ∈ V := vOf_mem S hmM
    rw [dif_pos hvV]
    have : (⟨vOf S m, hvV⟩ : ↥V) = d := Subtype.ext hvm
    rw [this, hd, C.cd_dc c hclt]
  ·
    unfold kap oneN
    rw [hTG0]
    have h1 : (1 : G) ∈ V := V.one_mem
    rw [bpart_one C S, cpart_V C S h1]
    have : C.cd ⟨1, h1⟩ = 0 := by
      have := C.cd_one
      exact this
    rw [this]
    rfl

end KapDef

end CFSG.Quasithin.H13.I1277

end
