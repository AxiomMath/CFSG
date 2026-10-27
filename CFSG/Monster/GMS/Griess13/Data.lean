module

public import CFSG.Sporadic.Co1
public import CFSG.Monster.GMS.Facts.Co1Module
import all CFSG.Blueprint.NativeSporadic
import all CFSG.Sporadic.HS.Group

public section

namespace CFSG.Monster.GMS.Griess13.Co1Data

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.SmallF2 (BaseFacts mA mB mA_pow mB_pow rowsMatrix rowsMatrix_rowsA
  rowsMatrix_rowsB seedEquiv closure_ab a_val b_val)
open scoped Matrix

abbrev G : Type := CFSG.Blueprint.NativeSporadic.Co1

abbrev mat (g : G) : Matrix (Fin 24) (Fin 24) (ZMod 2) := (g : Matrix (Fin 24) (Fin 24) (ZMod 2))

theorem mat_mul (g h : G) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : G) = 1 := rfl

theorem mat_injective : Function.Injective mat := fun _ _ h => Units.ext (Subtype.ext h)

theorem mat_inv_mul (g : G) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

theorem mat_mul_inv (g : G) : mat g * mat g⁻¹ = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

theorem mat_pow (g : G) (n : ℕ) : mat (g ^ n) = mat g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mat_one]
  | succ n ih => rw [pow_succ, pow_succ, mat_mul, ih]

theorem co1Act_apply (g : G) (v : Fin 24 → ZMod 2) :
    CFSG.Monster.GMS.co1Act g v = mat g *ᵥ v := rfl

abbrev dat : CFSG.Sporadic.SmallF2.Native.VecData := CFSG.Sporadic.Co1.Native.co1Data

theorem baseFacts :
    BaseFacts dat := CFSG.Sporadic.Co1.co1Facts.toBaseFacts

private theorem matA_eq : mA dat = decode 2 24 1 Co1Seed1 := rfl

private theorem matB_eq : mB dat = decode 2 24 1 Co1Seed2 := rfl

theorem rowsMatrix_rowsA_eq : rowsMatrix 24 dat.rowsA = decode 2 24 1 Co1Seed1 :=
  (rowsMatrix_rowsA dat).trans matA_eq

theorem rowsMatrix_rowsB_eq : rowsMatrix 24 dat.rowsB = decode 2 24 1 Co1Seed2 :=
  (rowsMatrix_rowsB dat).trans matB_eq

theorem decodeA_mul_self :
    decode 2 24 1 Co1Seed1 * decode 2 24 1 Co1Seed1 = 1 := by
  have h : mA dat ^ 2 = 1 := mA_pow baseFacts
  rwa [pow_two, matA_eq] at h

theorem decodeB_cube :
    decode 2 24 1 Co1Seed2 * (decode 2 24 1 Co1Seed2 * decode 2 24 1 Co1Seed2) = 1 := by
  have h : mB dat ^ 3 = 1 := mB_pow baseFacts
  rwa [pow_succ', pow_two, matB_eq] at h

theorem seedA_mem : decode 2 24 1 Co1Seed1 ∈ seedMonoid 2 24 1 Co1Seed1 Co1Seed2 :=
  Submonoid.subset_closure (Set.mem_insert _ _)

theorem seedB_mem : decode 2 24 1 Co1Seed2 ∈ seedMonoid 2 24 1 Co1Seed1 Co1Seed2 :=
  Submonoid.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

@[expose] noncomputable def genA : G :=
  ⟨⟨decode 2 24 1 Co1Seed1, seedA_mem⟩, ⟨decode 2 24 1 Co1Seed1, seedA_mem⟩,
    Subtype.ext decodeA_mul_self, Subtype.ext decodeA_mul_self⟩

@[expose] noncomputable def genB : G :=
  ⟨⟨decode 2 24 1 Co1Seed2, seedB_mem⟩,
    ⟨decode 2 24 1 Co1Seed2 * decode 2 24 1 Co1Seed2,
      (seedMonoid 2 24 1 Co1Seed1 Co1Seed2).mul_mem seedB_mem seedB_mem⟩,
    Subtype.ext decodeB_cube,
    Subtype.ext (by
      show decode 2 24 1 Co1Seed2 * decode 2 24 1 Co1Seed2 * decode 2 24 1 Co1Seed2 = 1
      rw [mul_assoc]
      exact decodeB_cube)⟩

theorem mat_genA : mat genA = decode 2 24 1 Co1Seed1 := rfl

theorem mat_genB : mat genB = decode 2 24 1 Co1Seed2 := rfl

theorem genA_mul_self : genA * genA = 1 :=
  mat_injective (by rw [mat_mul, mat_one]; exact decodeA_mul_self)

theorem genB_pow_three : genB ^ 3 = 1 :=
  mat_injective (by rw [mat_pow, mat_one, pow_succ', pow_two]; exact decodeB_cube)

private noncomputable def seedE : G ≃* CFSG.Sporadic.SmallF2.J dat :=
  seedEquiv (D := dat) baseFacts

private theorem seedE_val (g : G) :
    (((seedE g : CFSG.Sporadic.SmallF2.J dat) : GL (Fin dat.d) (ZMod 2)) :
      Matrix (Fin dat.d) (Fin dat.d) (ZMod 2)) = mat g :=
  rfl

theorem closure_gen :
    Subgroup.closure ({genA, genB} : Set G) = ⊤ := by
  have hA : seedE.symm (CFSG.Sporadic.SmallF2.a dat) = genA := by
    apply seedE.symm_apply_eq.2
    exact Subtype.ext (Units.ext (by rw [seedE_val, a_val baseFacts]; exact matA_eq.symm))
  have hB : seedE.symm (CFSG.Sporadic.SmallF2.b dat) = genB := by
    apply seedE.symm_apply_eq.2
    exact Subtype.ext (Units.ext (by rw [seedE_val, b_val baseFacts]; exact matB_eq.symm))
  rw [eq_top_iff]
  intro u _
  have hx : seedE u ∈ Subgroup.closure ({CFSG.Sporadic.SmallF2.a dat,
      CFSG.Sporadic.SmallF2.b dat} : Set (CFSG.Sporadic.SmallF2.J dat)) := by
    rw [closure_ab dat]; trivial
  have key : ∀ x ∈ Subgroup.closure ({CFSG.Sporadic.SmallF2.a dat,
      CFSG.Sporadic.SmallF2.b dat} : Set (CFSG.Sporadic.SmallF2.J dat)),
      seedE.symm x ∈ Subgroup.closure ({genA, genB} : Set G) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · rw [hA]; exact Subgroup.subset_closure (Set.mem_insert _ _)
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        rw [hB]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    | one => rw [map_one]; exact one_mem _
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact inv_mem hx
  have := key _ hx
  rwa [MulEquiv.symm_apply_apply] at this

@[expose] def letterOfChar (c : Char) : Option ℤ :=
  if c = 'a' then some 1 else if c = 'b' then some 2 else if c = 'c' then some 3
  else if c = 'A' then some (-1) else if c = 'B' then some (-2) else if c = 'C' then some (-3)
  else none

@[expose] def parseWord (s : String) : List ℤ := s.toList.filterMap letterOfChar

@[expose] def letterVal {M : Type} [Group M] (gens : List M) (l : ℤ) : M :=
  if 0 < l then gens.getD (l.toNat - 1) 1 else (gens.getD ((-l).toNat - 1) 1)⁻¹

@[expose] def evalWord {M : Type} [Group M] (gens : List M) (w : List ℤ) : M :=
  w.foldl (fun acc l => acc * letterVal gens l) 1

structure SLP where
  lines : List (ℕ × List (ℕ × ℤ))
  outs : List (ℕ × ℤ)

@[expose] def parseFactor (s : String) : ℕ × ℤ :=
  match s.splitOn "^" with
  | [r] => ((r.toNat?).getD 0, 1)
  | [r, e] => ((r.toNat?).getD 0, (e.toInt?).getD 0)
  | _ => (0, 0)

@[expose] def parseLine (s : String) : ℕ × List (ℕ × ℤ) :=
  match s.splitOn "=" with
  | [d, fs] => ((d.toNat?).getD 0, ((fs.splitOn " ").filter (· ≠ "")).map parseFactor)
  | _ => (0, [])

@[expose] def parseSLP (s : String) : SLP :=
  match s.splitOn "|" with
  | [body, outs] =>
    ⟨((body.splitOn ";").filter (· ≠ "")).map parseLine,
      ((outs.splitOn " ").filter (· ≠ "")).map parseFactor⟩
  | _ => ⟨[], []⟩

namespace SLP

@[expose] def init {M : Type} [Group M] (inputs : List M) : ℕ → M :=
  fun i => if 1 ≤ i then inputs.getD (i - 1) 1 else 1

@[expose] def step {M : Type} [Group M] (R : ℕ → M) (l : ℕ × List (ℕ × ℤ)) : ℕ → M :=
  Function.update R l.1 (l.2.foldl (fun acc f => acc * R f.1 ^ f.2) 1)

@[expose] def regs {M : Type} [Group M] (p : SLP) (inputs : List M) : ℕ → M :=
  p.lines.foldl step (init inputs)

@[expose] def eval {M : Type} [Group M] (p : SLP) (inputs : List M) : List M :=
  p.outs.map fun f => p.regs inputs f.1 ^ f.2

end SLP

@[expose] def slpMax11 : String :=
  "3=2^2;4=3 1;5=4 3;6=5 1;7=6^-1;8=7 1;9=1 6;10=8 8;11=10 3;12=11 9;13=12 3;14=13 1;15=14^\
    -1;16=15 2;17=3 14;18=17 9;19=18 9;20=19 17;21=20 2;22=21 9;23=22 3;24=23 1;25=24^-1;26=\
    25 2;27=3 24;28=8 26;29=28 16;30=29 3;31=30 26;32=31 1;33=32 16;34=33 26;35=34 16;36=35 \
    2;37=36 9;38=37 27;39=38 1;40=39^-1;41=40 40;42=41^-1;43=42 39;44=40 41;45=1 3;46=45 27;\
    47=46 1;48=47 17;49=48 9;50=49 16;51=50 16;52=51 2;53=52 9;54=53 1;55=54 17;56=55 1;57=5\
    6^-1;58=41 57;59=58 44;60=59 40;61=60 40;62=61^-1;63=62 56;64=57 61;65=64 57;66=65 43;67\
    =66 56;68=57 44;69=68 57;70=69 57;71=70 57;72=71 44;73=72 67;74=73 43;75=74 43;76=75 64;\
    77=76 43;78=77 64;79=78 44;80=79^-1;81=80 80;82=81^-1;83=82 79;84=80 81;85=39 56;86=85 4\
    4;87=86 64;88=87 64;89=88 44;90=89 67;91=90 44;92=91 56;93=92 63;94=93 63;95=94 44;96=95 \
    40;97=96^-1;98=83 79;99=98 97;100=99 84;101=100 80;102=101 80;103=102^-1;104=103 96;105=\
    97 102;106=105 83;107=106 104;108=84 104;109=108 79;110=109 83;111=110 105;112=111 107;1\
    13=112 96;114=113 84;115=114 97;116=115 97;117=116 83;118=117 79;119=118^-1;120=119 119;\
    121=120^-1;122=121 118;123=119 120;124=64 64;125=124 56;126=125 39;127=126 64;128=127 67\
    ;129=128 56;130=129 64;131=130 64;132=131 64;133=132 43;134=133 56;135=134 84;136=135 80\
    ;137=136 80;138=137 97;139=138 97;140=139 79;141=140^-1;142=120 141;143=142 123;144=143 \
    119;145=144 119;146=145^-1;147=146 140;148=141 145;149=80 118;150=149 141;151=150 122;15\
    2=151 104;153=152 119;154=82 96;155=154 83;156=155 105;157=156 83;158=157 153;159=158 79\
    ;160=159 105;161=160 80;162=161 104;163=162 96;164=163 83;165=164 140;166=165 148;167=16\
    6 141;168=167 148;169=168 118;170=122 140;171=170 169;172=171 119;173=172 147;174=123 14\
    8;175=174 140;176=175 140;177=176 118;178=177 173;179=178 123;180=179 141;181=180 118;18\
    2=181 148;183=182 118;184=183^-1;185=62 63;186=185 43;187=186 63;188=187 39;189=188^-1;1\
    90=97 104;191=190 96;192=191 105;193=192 97;194=193 79;195=194^-1;196=195 189;197=141 14\
    7;198=197 140;199=198 148;200=199 119;201=200^-1;202=201 196;203=184 184;204=203 169;205\
    =204 202;3=1 2;4=3 2;5=3 4;6=3 5;7=6 3;8=6 7;7=8 8;6=7 7;2=6 6;5=4 4;4=5^-1;6=4 2;2=6 5;\
    4=3 3;3=4^-1;6=3 1;1=6 4;3=1 2;4=3 2;5=3 3;6=4 5;7=4 3;8=6 5;1=8^4;9=8 5;8=4 6;6=8 9;3=6\
    ^3;6=2 2;8=4 4;9=5 8;5=9 9;2=6 5;5=2 7;2=5 4;4=2 7;2=4^-1;5=2 3;2=5 4;3=1 205|3 2"

@[expose] def slpMax2 : String :=
  "3=1 2;4=3 2;5=3 4;6=3 5;7=6 3;8=6 7;7=8 8;6=7 7;2=6 6;5=4 4;4=5^-1;6=4 2;2=6 5;4=3 3;3=4\
    ^-1;6=3 1;1=6 4|1 2"

@[expose] def slpWordsAB : String :=
  "4=1 1;5=3 4;6=1 5;7=2 3;8=7 2;9=8 6;10=9 5;11=10 6;12=1 3;13=10 12;14=1 2;15=11 11;16=13 \
    14;17=16 1;18=7 1;19=15 11;20=19 17;21=15 17;22=18 8;23=22 2;24=23 6;25=24 4;26=25 20;27\
    =26 21;28=2 1;29=13 12;30=29 1;31=30 27;32=16 28;33=18 27;34=31 31;35=14 14;36=16 2;37=3\
    6 33;38=11 32;39=7 3;40=32 38;41=37 31;42=39 28;43=7 42;44=43 8;45=44 35;46=45 14;47=46 \
    28;48=47 40;49=48 32;50=49 20;51=50 34;52=51 31;53=52 41;54=13 1;55=54 33;56=17 53;57=56 \
    56;58=36 28;59=55 55;60=58 53;61=37 55;62=8 4;63=57 57;64=3 5;65=17 11;66=37 61;67=63 60\
    ;68=64 39;69=68 2;70=69 12;71=70 5;72=71 40;73=72 21;74=73 65;75=74 59;76=75 66;77=76 11\
    ;78=77 53;79=78 67;80=58 38;81=62 79;82=4 1;83=55 31;84=16 33;85=59 59;86=85 55;87=29 8;\
    88=87 12;89=88 3;90=89 62;91=90 82;92=91 20;93=92 32;94=93 80;95=94 61;96=95 34;97=96 41\
    ;98=3^-1 2^-1;99=98 2^-1;100=99 3;101=58 11;102=101 58;103=81 86;104=31 59;105=97 16;106\
    =55 84;107=106 31;108=56 60;109=108 60;110=3^-1 2;111=110 8;112=100 2^-1;113=6 12 39 3 1 \
    80 102 34 55 34 83 84 34 36 103 63 16 42 7 14 4 2 14 12 1 102 32 58 17 104 104 34 105 10\
    3 67 56 54 8 1 39 64 62 17 15 15 58 32 65 107 66 105 81 60 57 109 56 36 2;114=4 3 28 7 2\
    ^-1 82 38 36 111 111 112 112 100 33 83 107 83 97 29 2 4 79 86 54 81 109 16|113 114"

@[expose] def eStr : Fin 6 → String :=
  !["baaabbaaaaaaBBaaabbb",
    "aaaaabbaaaaBAAAAbbbAAAAAAAAAbbaaaaaaaaabbb",
    "aaababaabbabbAAAAAAAAAbAAAAAAAAAbbaaaaaaaaabbb",
    "aaaaaaaaaBBAAAAAAAAABBBaaaaaaaaabAAAAAAAAAABBAABABBBAAABBB",
    "aaabaaaaaaBAAAAAAAAA",
    "BBaaaaaaaaaBBAAAAAAAAABBAAAAAAAAAAAAAAAAAAABAAAAABBBAAAABBA"]

@[expose] def tauStr : String :=
  "aaaaaaaaaBaaaaaaaaabaaaabAABBAAABBABaabAABBAAABBABAABBaaaabAABBAAABBABAAAAABAAAB"

@[expose] def mStr : Fin 2 → String :=
  !["BBaaaabAABBAAABBABAABBaaaabAABBAAABBABaabAABBAAABBABaabAABBAAABBABAABAABAAABBABBBAAB\
      BAAABBAAABABAABABBABAABBA",
    "BAAAAAAAAABBaaaaaaaaaBBAAAAAbAABBAAABBABAABaaaabAABBAAABBABAABBaaaabAABBAAABBABAABBa\
      aaabAABBAAABBABAABAbAABBBABBBABB"]

@[expose] def repStr : Fin 12 → String :=
  !["",
    "a",
    "b",
    "aa",
    "ab",
    "baa",
    "aab",
    "bab",
    "bbaa",
    "aaab",
    "baab",
    "abbaa"]

@[expose] def xStr : Fin 3 → String :=
  !["abababbaabbabaababaabaaababaaaabaaaaabaaabbbbaaaaaaaaabbAAAAAAAAA",
    "abaabbaaaabbbabaaaabaaabaaaaaaaababaaabaababaaabaaaaaaaababaaabaaaaaaaaaaabbaaaaaaaa\
      abbAAAAAAAAAbb",
    "BaaaaaaaaabaaaaaaaaaBaaaabAAABBAA"]

@[expose] def yStr : Fin 3 → String :=
  !["BBAABAAABABAAAAAAAABAAABABBAABAAABABAAAAAAAABAAABABBAAAbABAAAABABAAAABAABAAABAAAAABA\
      AAABABAAABAABAAAAbABAABABBA",
    "aaabbbaaabaaaBabaabaaaababaaaabaBaaabbAAAAAAAAAbAAAAAAAAAb",
    "aaaaaaaaaBBAAAAAAAAABBAAAAAAAAAAABAAABABAAAAAAAABAAABABAABAAABABAAAAAAAABAAABABAABAA\
      ABABAAAAAAAABAAABAAABAAABABAAAAAAAABAAABABBAABAAABABAAAAAAAABAAABAAAAABAABBBAABAAABA\
      AAAABAAABABAAAAAAAABAAABAAAABAAAAABAAAABABAAABAABAABABBAAABABBAB"]

@[expose] def gStr : String :=
  "abbabaaabbba"

@[expose] def mInS : List (List ℤ) :=
  [[7, 5, -3, -1, -5, 3, -7, -5, -1], [7, 2, 5, 3, 5, -1, -1, 3, 3, -5, -7]]

@[expose] def actA1 : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![1, 0, 0, 0, 0, 0;
    1, 2, 1, 2, 2, 2;
    2, 2, 0, 1, 2, 2;
    1, 2, 2, 0, 1, 0;
    2, 1, 1, 1, 1, 1;
    0, 2, 2, 1, 1, 1]

@[expose] def actA2 : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![1, 2, 0, 0, 0, 2;
    0, 1, 0, 0, 0, 0;
    0, 0, 2, 0, 1, 2;
    2, 2, 0, 2, 0, 2;
    1, 2, 2, 1, 2, 2;
    2, 0, 1, 2, 2, 1]

@[expose] def actN : Fin 2 → Matrix (Fin 6) (Fin 6) (ZMod 3) := ![actA1, actA2]

@[expose] def w1 : Fin 6 → ZMod 3 :=
  ![1, 1, 0, 0, 0, 1]

@[expose] def v0 : Fin 6 → ZMod 3 :=
  ![0, 0, 0, 0, 0, 1]

@[expose] def repw : Fin 12 → Fin 6 → ZMod 3 :=
  ![![1, 1, 0, 0, 0, 1],
    ![1, 1, 2, 0, 2, 2],
    ![1, 2, 1, 0, 1, 0],
    ![1, 2, 0, 0, 1, 0],
    ![1, 1, 0, 2, 0, 2],
    ![1, 2, 2, 2, 0, 1],
    ![1, 2, 2, 0, 2, 1],
    ![1, 1, 1, 0, 0, 2],
    ![1, 1, 1, 2, 0, 1],
    ![1, 2, 2, 2, 0, 0],
    ![1, 2, 2, 2, 2, 1],
    ![1, 1, 2, 2, 1, 1]]

@[expose] def actP : Fin 2 → Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  ![!![0, 1, 1, 0, 2, 0;
    2, 1, 0, 0, 1, 1;
    0, 1, 2, 0, 1, 2;
    2, 1, 1, 1, 2, 0;
    1, 2, 2, 0, 2, 0;
    0, 2, 2, 0, 2, 2],
    !![2, 0, 2, 1, 0, 2;
    2, 2, 0, 2, 2, 0;
    2, 0, 0, 1, 0, 1;
    2, 2, 2, 1, 0, 2;
    2, 1, 0, 0, 2, 0;
    0, 2, 0, 2, 0, 2]]

@[expose] def actR : Fin 12 → Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  ![!![1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0, 0;
    1, 2, 1, 2, 2, 2;
    2, 2, 0, 1, 2, 2;
    1, 2, 2, 0, 1, 0;
    2, 1, 1, 1, 1, 1;
    0, 2, 2, 1, 1, 1],
    !![1, 2, 0, 0, 0, 2;
    0, 1, 0, 0, 0, 0;
    0, 0, 2, 0, 1, 2;
    2, 2, 0, 2, 0, 2;
    1, 2, 2, 1, 2, 2;
    2, 0, 1, 2, 2, 1],
    !![1, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 1;
    0, 0, 1, 2, 0, 2;
    0, 0, 0, 1, 0, 0;
    2, 0, 0, 2, 1, 0;
    0, 1, 1, 2, 2, 1],
    !![0, 2, 0, 0, 0, 0;
    1, 2, 1, 2, 2, 2;
    0, 0, 2, 2, 1, 1;
    0, 0, 1, 0, 2, 0;
    0, 1, 1, 1, 1, 0;
    1, 1, 2, 1, 1, 2],
    !![1, 2, 0, 0, 0, 2;
    1, 2, 1, 2, 2, 2;
    2, 1, 1, 2, 2, 2;
    2, 2, 0, 2, 0, 2;
    1, 1, 2, 2, 2, 1;
    2, 0, 1, 2, 1, 2],
    !![2, 1, 2, 1, 1, 1;
    2, 1, 0, 0, 0, 1;
    2, 2, 1, 1, 2, 0;
    0, 1, 2, 0, 1, 1;
    0, 1, 1, 1, 0, 2;
    0, 1, 2, 1, 1, 0],
    !![0, 2, 0, 0, 0, 0;
    2, 0, 2, 1, 0, 2;
    1, 0, 1, 1, 0, 2;
    2, 1, 0, 2, 2, 0;
    0, 2, 1, 0, 0, 0;
    2, 1, 2, 1, 2, 0],
    !![2, 1, 2, 1, 1, 1;
    2, 0, 2, 1, 0, 2;
    0, 1, 2, 1, 0, 1;
    1, 1, 2, 2, 1, 1;
    0, 2, 0, 2, 2, 0;
    2, 1, 0, 0, 1, 2],
    !![1, 2, 0, 0, 0, 2;
    0, 1, 0, 0, 0, 0;
    2, 1, 0, 1, 0, 2;
    1, 0, 1, 0, 2, 2;
    1, 1, 1, 2, 1, 0;
    2, 0, 1, 2, 2, 1],
    !![1, 0, 1, 2, 0, 1;
    1, 2, 1, 2, 2, 2;
    0, 0, 0, 1, 2, 0;
    0, 0, 1, 0, 0, 1;
    0, 0, 1, 0, 2, 0;
    0, 2, 0, 0, 1, 2],
    !![1, 2, 0, 0, 0, 2;
    1, 1, 0, 1, 1, 0;
    0, 1, 2, 2, 2, 1;
    1, 1, 2, 0, 1, 2;
    2, 1, 2, 0, 2, 0;
    2, 1, 0, 2, 2, 2]]

@[expose] def wB : Fin 6 → ZMod 3 := ![0, 0, 1, 0, 0, 0]

@[expose] def wC : Fin 6 → ZMod 3 := ![1, 0, 0, 0, 0, 0]

@[expose] def decTable : List (ℕ × String × ℕ × String) :=
  [(1, "000000", 0, ""),
   (1, "000001", 0, ""),
   (3, "000000", 0, ""),
   (3, "000001", 0, ""),
   (4, "000000", 0, ""),
   (4, "000001", 0, ""),
   (0, "222021", 0, "BBaBaBaBaBABABBBABBABABA"),
   (0, "222022", 0, "BBaBaBaBaBABABBBABBABABA"),
   (6, "000000", 0, ""),
   (6, "000001", 0, ""),
   (2, "112201", 1, "BabaBaBaBABA"),
   (2, "221211", 1, "BabaBaBaBABA"),
   (9, "000000", 0, ""),
   (9, "000001", 0, ""),
   (5, "111012", 1, "bbbabbababbababab"),
   (5, "012002", 1, "bbbabbababbababab"),
   (11, "000000", 0, ""),
   (11, "000001", 0, ""),
   (7, "001122", 0, "BBabbaBabbABBAB"),
   (7, "120220", 0, "BBabbaBabbABBAB"),
   (10, "020210", 0, "ababbababbAbABAbA"),
   (10, "122210", 0, "ababbababbAbABAbA"),
   (8, "200000", 0, "bbbabbabababaBAbAbAbA"),
   (8, "011122", 0, "bbbabbabababaBAbAbAbA"),
   (2, "000000", 0, ""),
   (2, "000001", 0, ""),
   (3, "220122", 1, "BBaBaBaBabABABBBA"),
   (3, "110200", 1, "BBaBaBaBabABABBBA"),
   (0, "011202", 0, "BBaBaBaBaBBABBABABABBBABA"),
   (0, "112112", 0, "BBaBaBaBaBBABBABABABBBABA"),
   (5, "000000", 0, ""),
   (5, "000001", 0, ""),
   (7, "000000", 0, ""),
   (7, "000001", 0, ""),
   (8, "000000", 0, ""),
   (8, "000001", 0, ""),
   (10, "000000", 0, ""),
   (10, "000001", 0, ""),
   (4, "200111", 0, "abaBaBaBBABABAB"),
   (4, "022022", 0, "abaBaBaBBABABAB"),
   (1, "102202", 1, "abbbabaBAbAbAbAbb"),
   (1, "002022", 1, "abbbabaBAbAbAbAbb"),
   (6, "120210", 0, "bbabbbababbAbABAbAbb"),
   (6, "122101", 0, "bbabbbababbAbABAbAbb"),
   (11, "210020", 1, "abaBabbaBABBBA"),
   (11, "212202", 1, "abaBabbaBABBBA"),
   (9, "022101", 1, "BBBabaB"),
   (9, "200110", 1, "BBBabaB")]

@[expose] def tmatBits : String :=
  "101011000000001101000101110110100000110010000111001100000110101010110000\
    001100001110101101101100111100111001110100101110000010111011100001011001\
    000010010110011110011011011110000101011100011000101110110100011000110101\
    111100111111101001000001010000001111000001110101111011010101100101110110\
    110111001111111011101111111010111111110010000001011110111010111111011000\
    001010101011001110110010110000100000101001000111100010010010100110011100\
    100011110011000111011111011010011000101111110111100111001000111101000110\
    001011110101001100110001100000110110000010000100001111110010100100000000\
    001100111111110000001001111111111100011010011101001111010110101010010001\
    111001001100101110110110001010100000101111100010001011011000101101001111\
    000000101111101011000000111011110010011101000011001101000111110010100100\
    001111111001000001010001000110110000110100101011111000110100101100011011\
    000000000000000000000000000001111000000010101101111101000010101001101000\
    001010100000101111100010110001111101011001100001110000101010110000001100\
    110101110011011110111111001001001001110101111010110000101010110000001100\
    001001001001110101111010000110011111011111101011000000101111101011000000\
    110111101010100011100001100000000010011101001110001101011001111101000000\
    111100110000101000100010000110101011101001111100011011011001110101010111\
    010111111101000101010110000100111000100001101101010111000001111100111111\
    100100010110000000101101101111100101110111011010100101001010101001110100\
    100100110100101010010110100110000010111010000011110011011001110110100010\
    000000001101000011000111001111100101001011110000000001000010001011000001\
    011010001110101010100110110001000010100101101111001011001100010000100011\
    111000101000010000011000111101100011100110001110010011110011010010100000\
    001111110001100100111010101100111101101101000111110111111100001001101110\
    110101010110110110011000000100111010110001001001010010010000000000101101\
    101101011000110001111000001100001001010110111010010000001001001010111001\
    100000011000000111110011010000011001101101000111010000111001110111001011\
    101111000011101100011001010101101110111011010111111011101000000001110101\
    111110001001011011110111111110110111111001010001000000111010001001101100\
    100111100011101000001110110110001010010011101001000101001101010011011111\
    111000000111111011011000001111110111100101110111101101110111001010010000\
    101010101000001001000100000010100110101111100000110100101101100100100111\
    100110111001010000001001011011001100110010101011000111011010110001011000\
    111101100111100101111100001010010111011000110111101000110000111110011011\
    000010010011101110010000100001100001010111110100000100011101111110011011\
    111100010111110110100000011010010011110110101000001100011001001000111100\
    011111011011010111111011000000101101100001111010000010110100101000111110\
    011001110000001011100100010010111011100011110001001010101001000000001000\
    000000111111011010111011101100011010110111010101001010101001000000001000\
    101101110111110101010101110010011110101011100111101001111010000111100010\
    111101110100110111001000111010100100010111100010111000000000100100011110\
    100110000011000110110011100011110011001000100001110100011001100010100000\
    011010011010100101001001101001000110110001011100001000100111010100100001\
    110100111100100001111110010100001100100110001111100101000011111100001010\
    001110001111110110100110100011101101010101101100011011110011101100111111\
    101010000001100011001000110000010111100101111110111010101100101001011001\
    111110101001100101010101111000110010100111111010000100000000110010000100\
    011101010111101110001010101111001100011100111110001110110001001011001100\
    011110001100000110100011001101000110100001010111100110011111010001000000\
    111011011001110110110110010111011001010000010100101101011011001101001101\
    011101000100001110010010110101000111011101000101111111011001010110111101\
    101100011111011101001000000011000100100110010111110010010001100111001100\
    111001011100001011111000001001010101100001000100100001001100011110111110\
    011001101100111010010000100000110110101010100001000010000000101001000100\
    110101100110100110100011001100101100101010111011101010111010110000000010\
    100000000000000000000000010000000000000000000000001000000000000000000000\
    000100000000000000000000000010000000000000000000000001000000000000000000\
    000000100000000000000000000000010000000000000000000000001000000000000000\
    000000000100000000000000000000000010000000000000000000000001000000000000\
    000000000000100000000000000000000000010000000000000000000000001000000000\
    000000000000000100000000000000000000000010000000000000000000000001000000\
    000000000000000000100000000000000000000000010000000000000000000000001000\
    000000000000000000000100000000000000000000000010000000000000000000000001"

@[expose] def freePos : List ℕ := [567, 569, 570, 571, 572, 573, 574, 575]

@[expose] noncomputable def nOut :
    List G := (parseSLP slpMax11).eval [genA, genB]

@[expose] noncomputable def n1 : G := nOut.getD 0 1

@[expose] noncomputable def n2 : G := nOut.getD 1 1

@[expose] noncomputable def nGen : Fin 2 → G := ![n1, n2]

@[expose] noncomputable def N :
    Subgroup G := Subgroup.closure {n1, n2}

@[expose] noncomputable def wN
    (s : String) : G := evalWord [n1, n2] (parseWord s)

@[expose] noncomputable def e (i : Fin 6) : G := wN (eStr i)

@[expose] def iotaOf {M : Type} [Group M] (ε : Fin 6 → M) (v : Fin 6 → ZMod 3) : M :=
  (List.ofFn fun i => ε i ^ (v i).val).prod

@[expose] noncomputable def iota
    (v : Fin 6 → ZMod 3) : G := iotaOf e v

@[expose] noncomputable def tau : G := wN tauStr

@[expose] noncomputable def m (i : Fin 2) : G := wN (mStr i)

@[expose] noncomputable def cm : G := (m 0)⁻¹ * (m 1)⁻¹ * m 0 * m 1

@[expose] noncomputable def cConj (g : G) : G := g⁻¹ * cm * g

@[expose] noncomputable def S : List G :=
  [cm, cConj (m 0), cConj (m 1), cConj (m 0)⁻¹, cConj (m 1)⁻¹, cConj (m 0 * m 1),
    cConj (m 1 * m 0)]

@[expose] noncomputable def P :
    Subgroup G := Subgroup.closure {m 0, m 1}

@[expose] noncomputable def r (k : Fin 12) : G := wN (repStr k)

@[expose] noncomputable def e0 : G := iota v0

@[expose] noncomputable def wM
    (s : String) : G := evalWord [m 0, m 1] (parseWord s)

@[expose] def decRec (s : Fin 2) (k : Fin 12) (j : Fin 2) : ℕ × String × ℕ × String :=
  decTable.getD (24 * s.val + 2 * k.val + j.val) (0, "000000", 0, "")

@[expose] def decSigma (s : Fin 2) (k : Fin 12) (j : Fin 2) : Fin 12 :=
  Fin.ofNat 12 (decRec s k j).1

@[expose] def decU (s : Fin 2) (k : Fin 12) (j : Fin 2) : Fin 6 → ZMod 3 :=
  fun i => (((decRec s k j).2.1.toList.getD i.val '0').toNat - '0'.toNat : ℕ)

@[expose] def decEps (s : Fin 2) (k : Fin 12) (j : Fin 2) : ℕ := (decRec s k j).2.2.1

@[expose] noncomputable def decP
    (s : Fin 2) (k : Fin 12) (j : Fin 2) : G :=
  wM (decRec s k j).2.2.2

@[expose] noncomputable def hOut :
    List G := (parseSLP slpMax2).eval [genA, genB]

@[expose] noncomputable def g : G := evalWord hOut (parseWord gStr)

@[expose] noncomputable def xGen (k : Fin 3) : G := wN (xStr k)

@[expose] noncomputable def yGen (k : Fin 3) : G := wN (yStr k)

@[expose] def Tmat (i : Fin 8) : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  decode 2 24 1 ("T\n" ++ (tmatBits.drop (576 * i.val)).take 576)

@[expose] noncomputable def abOut :
    List G := (parseSLP slpWordsAB).eval [n1, n2, g]

end CFSG.Monster.GMS.Griess13.Co1Data
